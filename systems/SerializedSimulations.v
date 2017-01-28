Require Import StructTact.Util.
Require Import Verdi.Verdi.
Require Import FunctionalExtensionality.
Require Import Verdi.TotalMapSimulations.
Require Import Verdi.PartialMapSimulations.
Require Import Serialized.
Require Import Cheerios.Core.

Require Import mathcomp.ssreflect.ssreflect.

Section SerializedCorrect.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.

  Context {orig_failure_params : FailureParams orig_multi_params}.

  Context {orig_name_overlay_params : NameOverlayParams orig_multi_params}.
  Context {orig_fail_msg_params : FailMsgParams orig_multi_params}.
  Context {orig_new_msg_params : NewMsgParams orig_multi_params}.

  Context {orig_input_serializer : Serializer input}.
  Context {orig_output_serializer : Serializer output}.
  Context {orig_msg_serializer : Serializer msg}.

  (* total map simulations *)

  Definition serialize_packet p :=
    @mkPacket _ serialized_multi_params
              (@pSrc _ orig_multi_params p)
              (pDst p)
              (serialize (pBody p)).

  Definition serialize_net (net : @network _ orig_multi_params) : (@network _ serialized_multi_params) :=
    @mkNetwork _ serialized_multi_params (map serialize_packet (nwPackets net)) net.(nwState).

  Definition serialize_tr_entry (e : @name _ orig_multi_params * (@input orig_base_params + list (@output orig_base_params))) :
    @name _ serialized_multi_params * (@input serialized_base_params + list (@output serialized_base_params)) :=
  let (n, s) := e in
  match s with
  | inl io => (n, inl (serialize io))
  | inr lo => (n, inr (map serialize lo))
  end.

  Instance orig_multi_params_name_tot_map :
    MultiParamsNameTotalMap orig_multi_params serialized_multi_params :=
  {
    tot_map_name := id ;
    tot_map_name_inv := id
  }.

  Instance orig_multi_params_name_tot_map_bijective :
    MultiParamsNameTotalMapBijective orig_multi_params_name_tot_map :=
  {
    tot_map_name_inv_inverse := fun _ => eq_refl ;
    tot_map_name_inverse_inv := fun _ => eq_refl
  }.

  Instance orig_base_params_tot_map :
    BaseParamsTotalMap orig_base_params serialized_base_params :=
  {
    tot_map_data := id;
    tot_map_input := serialize;
    tot_map_output := serialize
  }.

  Instance orig_multi_params_tot_msg_map :
    MultiParamsMsgTotalMap orig_multi_params serialized_multi_params :=
  {
    tot_map_msg := serialize
  }.

  Instance orig_failure_params_tot_map_congruency : FailureParamsTotalMapCongruency orig_failure_params serialized_failure_params orig_base_params_tot_map :=
    {
      tot_reboot_eq := fun _ => eq_refl
    }.

  Instance orig_multi_name_overlay_params_tot_map_congruency : NameOverlayParamsTotalMapCongruency orig_name_overlay_params serialized_name_overlay_params orig_multi_params_name_tot_map := 
  {
    tot_adjacent_to_fst_snd := fun _ _ => conj (fun H => H) (fun H => H)
  }.

  Instance orig_multi_fail_msg_params_tot_map_congruency : FailMsgParamsTotalMapCongruency orig_fail_msg_params serialized_fail_msg_params orig_multi_params_tot_msg_map :=
  {
    tot_fail_msg_fst_snd := eq_refl
  }.

  Instance orig_multi_new_msg_params_tot_map_congruency : NewMsgParamsTotalMapCongruency orig_new_msg_params serialized_new_msg_params orig_multi_params_tot_msg_map :=
  {
    tot_new_msg_fst_snd := eq_refl
  }.

  Instance orig_multi_params_map_congruency :
    MultiParamsTotalMapCongruency orig_base_params_tot_map
      orig_multi_params_name_tot_map orig_multi_params_tot_msg_map :=
  {
    tot_init_handlers_eq := fun _ => eq_refl ;
    tot_net_handlers_eq := _ ;
    tot_input_handlers_eq := _
  }.
  Proof.
  - move => me src m st.
    rewrite /tot_mapped_net_handlers /= /tot_map_name_msgs /= /id /=.
    repeat break_let.
    rewrite /serialized_net_handlers.
    rewrite serialize_deserialize_id_nil.
    rewrite /serialize_handler_result.
    repeat break_let.
    find_injection.
    set l1 := map _ l.
    set l2 := map _ l.
    suff H_suff: l1 = l2 by rewrite H_suff.
    rewrite /l1 /l2.
    clear.
    elim: l => //=.
    move => p l IH.
    rewrite IH /= /serialize_name_msg_tuple /=.
    by break_let.
  - move => me inp st.
    rewrite /tot_mapped_input_handlers /=.
    repeat break_let.
    unfold serialized_input_handlers in *.
    rewrite serialize_deserialize_id_nil.
    rewrite /serialize_handler_result /id /tot_map_name_msgs /tot_map_name /= /id /=.
    repeat break_let.
    find_injection.
    set l1 := map _ l.
    set l2 := map _ l.
    suff H_suff: l1 = l2 by rewrite H_suff.
    rewrite /l1 /l2.
    clear.
    elim: l => //=.
    move => p l IH.
    rewrite IH /= /serialize_name_msg_tuple /=.
    by break_let.
  Qed.

  Lemma step_async_serialize_simulation :
    forall net net' tr,
      @step_async _ orig_multi_params net net' tr ->
      @step_async _ serialized_multi_params (serialize_net net) (serialize_net net') (map serialize_tr_entry tr).
  Proof.
  move => net net' out H_step.
  apply step_async_tot_mapped_simulation_1 in H_step.
  rewrite /tot_map_name /tot_map_net /= /id /= in H_step.
  rewrite /tot_map_trace_occ /= /id /= in H_step.
  rewrite /tot_map_packet /= /id /= in H_step.
  rewrite /serialize_net.
  move: H_step.
  set fp := fun p : packet => _.
  have H_eq: fp = serialize_packet by rewrite /fp ; apply functional_extensionality; case => /= src dst m.
  by rewrite H_eq {H_eq fp}. 
  Qed.

  Lemma step_async_serialize_simulation_star :
    forall net tr,
      @step_async_star _ orig_multi_params step_async_init net tr ->
      @step_async_star _ serialized_multi_params step_async_init (serialize_net net) (map serialize_tr_entry tr).
  Proof.
  move => net tr H_step.
  apply step_async_tot_mapped_simulation_star_1 in H_step.
  rewrite /tot_map_name /tot_map_net /= /id /= in H_step.
  rewrite /tot_map_trace_occ /= /id /= in H_step.
  rewrite /tot_map_packet /= /id /= in H_step.
  rewrite /serialize_net.
  move: H_step.
  set fp := fun p : packet => _.
  have H_eq: fp = serialize_packet by rewrite /fp ; apply functional_extensionality; case => /= src dst m.
  by rewrite H_eq {H_eq fp}. 
  Qed.

  Lemma step_failure_serialize_simulation :
    forall net net' failed failed' tr,
      @step_failure _ _ orig_failure_params (failed, net) (failed', net') tr ->
      @step_failure _ _ serialized_failure_params (failed, serialize_net net) (failed', serialize_net net') (map serialize_tr_entry tr).
  Proof.
  move => net net' failed failed' tr H_step.
  apply step_failure_tot_mapped_simulation_1 in H_step.
  rewrite /tot_map_name /tot_map_net /= /id /= in H_step.
  rewrite /tot_map_trace_occ /= /id /= in H_step.
  rewrite /tot_map_packet /= /id /= in H_step.
  rewrite /serialize_net.
  move: H_step.
  rewrite 2!map_id.
  set fp := fun p : packet => _.
  have H_eq: fp = serialize_packet by rewrite /fp ; apply functional_extensionality; case => /= src dst m.
  by rewrite H_eq {H_eq fp}. 
  Qed.

  Lemma step_failure_serialize_simulation_star :
    forall net failed tr,
      @step_failure_star _ _ orig_failure_params step_failure_init (failed, net) tr ->
      @step_failure_star _ _ serialized_failure_params step_failure_init (failed, serialize_net net) (map serialize_tr_entry tr).
  Proof.
  move => net failed tr H_step.
  apply step_failure_tot_mapped_simulation_star_1 in H_step.
  rewrite /tot_map_name /tot_map_net /= /id /= in H_step.
  rewrite /tot_map_trace_occ /= /id /= in H_step.
  rewrite /tot_map_packet /= /id /= in H_step.
  rewrite /serialize_net.
  move: H_step.
  rewrite map_id.
  set fp := fun p : packet => _.
  have H_eq: fp = serialize_packet by rewrite /fp ; apply functional_extensionality; case => /= src dst m.  
  by rewrite H_eq {H_eq fp}.
  Qed.  

  Lemma step_ordered_failure_serialize_simulation :
  forall net net' failed failed' tr,
    @step_ordered_failure _ _ orig_name_overlay_params orig_fail_msg_params (failed, net) (failed', net') tr ->
    @step_ordered_failure _ _ serialized_name_overlay_params serialized_fail_msg_params (failed, tot_map_onet net) (failed', tot_map_onet net') (map tot_map_trace tr).
  Proof.
  move => net net' failed failed' tr H_step.
  have H_eq_n: failed = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n.
  have H_eq_n': failed' = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed' by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n'.
  exact: step_ordered_failure_tot_mapped_simulation_1.
  Qed.

  Lemma step_ordered_failure_serialize_simulation_star :
  forall net failed tr,
    @step_ordered_failure_star _ _ orig_name_overlay_params orig_fail_msg_params step_ordered_failure_init (failed, net) tr ->
    @step_ordered_failure_star _ _ serialized_name_overlay_params serialized_fail_msg_params step_ordered_failure_init (failed, tot_map_onet net) (map tot_map_trace tr).
  Proof.
  move => net failed tr H_st.
  have ->: failed = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  exact: step_ordered_failure_tot_mapped_simulation_star_1.
  Qed.

  Lemma step_ordered_dynamic_failure_serialize_simulation :
  forall net net' failed failed' tr,
    NoDup (odnwNodes net) ->
    @step_ordered_dynamic_failure _ _ orig_name_overlay_params orig_new_msg_params orig_fail_msg_params (failed, net) (failed', net') tr ->
    @step_ordered_dynamic_failure _ _ serialized_name_overlay_params serialized_new_msg_params serialized_fail_msg_params (failed, tot_map_odnet net) (failed', tot_map_odnet net') (map tot_map_trace tr).
  Proof.
  move => net net' failed failed' tr H_nd H_step.
  have H_eq_n: failed = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n.
  have H_eq_n': failed' = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed' by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n'.
  exact: step_ordered_dynamic_failure_tot_mapped_simulation_1.
  Qed.

  Lemma step_ordered_dynamic_failure_serialize_simulation_star :
  forall net failed tr,
    @step_ordered_dynamic_failure_star _ _ orig_name_overlay_params orig_new_msg_params orig_fail_msg_params step_ordered_dynamic_failure_init (failed, net) tr ->
    @step_ordered_dynamic_failure_star _ _ serialized_name_overlay_params serialized_new_msg_params serialized_fail_msg_params step_ordered_dynamic_failure_init (failed, tot_map_odnet net) (map tot_map_trace tr).
  Proof.
  move => net failed tr H_st.
  have ->: failed = map (@tot_map_name _ _ _ _ orig_multi_params_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  exact: step_ordered_dynamic_failure_tot_mapped_simulation_star_1.
  Qed.

  (* partial map simulation *)

  Definition deserialize_packet (p : @packet _ serialized_multi_params) : option (@packet _ orig_multi_params) :=
    match (deserialize (pBody p)) with
    | None => None
    | Some (body, _) =>
      Some (@mkPacket _ orig_multi_params (pSrc p) (pDst p) body)
    end.

  Definition deserialize_net (net: @network _ serialized_multi_params) :  (@network _ orig_multi_params) :=
    mkNetwork (filterMap deserialize_packet (nwPackets net)) net.(nwState).

  Definition deserialize_tr_entry (e : @name _ serialized_multi_params * (@input serialized_base_params + list (@output serialized_base_params))) :
    option (@name _ orig_multi_params * (@input orig_base_params + list (@output orig_base_params))) :=
  let (n, s) := e in
  match s with
  | inl i => 
    match deserialize i with
    | Some (data, _) => Some (n, inl data)
    | None => None
    end
  | inr lo => Some (n, inr (filterMap (fun o => match deserialize o with Some (data, _) => Some data | None => None end) lo))
  end.

  Lemma deserialize_serialize_net_id : forall net,
      deserialize_net (serialize_net net) = net.
  Proof.
  case => ps nwS.
  rewrite /deserialize_net /serialize_net /=.
  set ps' := filterMap _ _.
  have H_p: ps' = ps.
    rewrite /ps'.
    clear.
    rewrite /deserialize_packet.
    elim: ps => [|p ps IH] //=.
    rewrite serialize_deserialize_id_nil IH.
    by case: p.
  by rewrite H_p.
  Qed.

  Lemma filterMap_deserialize_tr_entry_map_serialize_id :
    forall tr, filterMap deserialize_tr_entry (map serialize_tr_entry tr) = tr.
  Proof.
  elim => //=.
  case => n. 
  case => [i|o] l IH; rewrite /deserialize_tr_entry /serialize_tr_entry /=.
  - by rewrite serialize_deserialize_id_nil /= IH.
  - rewrite IH.
    set fMo := filterMap _ _.
    suff H_suff: fMo = o by rewrite H_suff.
    rewrite /fMo.
    clear.
    elim: o => //=.
    move => o l IH.
    by rewrite serialize_deserialize_id_nil /= IH.
  Qed.

  Instance multi_params_orig_name_tot_map :
    MultiParamsNameTotalMap serialized_multi_params orig_multi_params :=
  {
    tot_map_name := id ;
    tot_map_name_inv := id
  }.

  Instance multi_params_orig_name_tot_map_bijective :
    MultiParamsNameTotalMapBijective multi_params_orig_name_tot_map :=
  {
    tot_map_name_inv_inverse := fun _ => eq_refl ;
    tot_map_name_inverse_inv := fun _ => eq_refl
  }.

  Instance multi_orig_params_pt_msg_map : MultiParamsMsgPartialMap serialized_multi_params orig_multi_params :=
  {
    pt_map_msg := fun m => 
      match deserialize m with 
      | Some (data, _) => Some data
      | None => None
      end   
  }.

  Instance multi_orig_base_params_pt_map : BaseParamsPartialMap serialized_base_params orig_base_params :=
  {
    pt_map_data := id;
    pt_map_input := fun i =>
                     match deserialize i with 
                     | Some (data, _) => Some data
                     | None => None
                     end;
    pt_map_output := fun o =>
                     match deserialize o with 
                     | Some (data, _) => Some data
                     | None => None
                     end
  }.

  Instance multi_orig_failure_params_pt_map_congruency : FailureParamsPartialMapCongruency serialized_failure_params orig_failure_params multi_orig_base_params_pt_map :=
    {
      pt_reboot_eq := fun _ => eq_refl
    }.

  Instance multi_orig_name_overlay_params_tot_map_congruency : NameOverlayParamsTotalMapCongruency serialized_name_overlay_params orig_name_overlay_params multi_params_orig_name_tot_map := 
  {
    tot_adjacent_to_fst_snd := fun _ _ => conj (fun H => H) (fun H => H)
  }.

  Instance multi_orig_fail_msg_params_pt_map_congruency : FailMsgParamsPartialMapCongruency serialized_fail_msg_params orig_fail_msg_params multi_orig_params_pt_msg_map :=
  {
    pt_fail_msg_fst_snd := _
  }.
  Proof.
  rewrite /pt_map_msg /=.
  by rewrite serialize_deserialize_id_nil.
  Qed.

  Instance multi_orig_new_msg_params_pt_map_congruency : NewMsgParamsPartialMapCongruency serialized_new_msg_params orig_new_msg_params multi_orig_params_pt_msg_map :=
  {
    pt_new_msg_fst_snd := _
  }.
  Proof.
  rewrite /pt_map_msg /=.
  by rewrite serialize_deserialize_id_nil.
  Qed.

  Instance multi_orig_params_pt_map_congruency : MultiParamsPartialMapCongruency multi_orig_base_params_pt_map multi_params_orig_name_tot_map multi_orig_params_pt_msg_map :=
  {
    pt_init_handlers_eq := fun _ => eq_refl ;
    pt_net_handlers_some := _ ;
    pt_net_handlers_none := _ ;
    pt_input_handlers_some := _ ;
    pt_input_handlers_none := _
  }.
  Proof.
  - move => me src mg st mg' H_eq.
    rewrite /pt_mapped_net_handlers.
    repeat break_let.
    rewrite /tot_map_name /= /id.
    rewrite /pt_map_msg /= in H_eq.
    rewrite /net_handlers /= /serialized_net_handlers in Heqp.
    move: H_eq Heqp.
    case H_m: (deserialize mg) => [m'|] => H_eq //.
    break_let.
    find_injection.
    rewrite /serialize_handler_result in Heqp.
    repeat break_let.
    find_injection.
    set sl3 := pt_map_outputs _.
    set sl2 := pt_map_name_msgs _.
    have H_eq: sl3 = l3.
      rewrite /sl3 /pt_map_outputs.
      clear.
      elim: l3 => //=.
      move => o l IH.
      by rewrite serialize_deserialize_id_nil IH.
    have H_eq': sl2 = l2.
      rewrite /sl2 /pt_map_name_msgs /tot_map_name /id /= /id /serialize_name_msg_tuple.
      clear.
      elim: l2 => //=.
      case => [n m] => /=.
      move => l IH.
      by rewrite serialize_deserialize_id_nil IH.
    by rewrite H_eq H_eq'.
  - move => me src mg st out st' ps H_eq H_eq'.
    rewrite /net_handlers /= /serialized_net_handlers /= in H_eq'.
    rewrite /pt_map_msg /= in H_eq.
    move: H_eq H_eq'.
    case H_eq_m: (deserialize mg) => [mg'|] H_eq H_eq'; first by repeat break_let.
    by find_injection.
  - move => me inp st inp' H_eq.
    rewrite /pt_mapped_input_handlers.
    repeat break_let.
    rewrite /tot_map_name /= /id.
    rewrite /pt_map_input /= in H_eq.
    rewrite /input_handlers /= /serialized_input_handlers in Heqp.
    move: H_eq Heqp.
    case H_m: (deserialize inp) => [i|] => H_eq //.
    break_let.
    find_injection.
    rewrite /serialize_handler_result in Heqp.
    repeat break_let.
    find_injection.
    set sl3 := pt_map_outputs _.
    set sl2 := pt_map_name_msgs _.
    have H_eq: sl3 = l3.
      rewrite /sl3 /pt_map_outputs.
      clear.
      elim: l3 => //=.
      move => o l IH.
      by rewrite serialize_deserialize_id_nil IH.
    have H_eq': sl2 = l2.
      rewrite /sl2 /pt_map_name_msgs /tot_map_name /id /= /id /serialize_name_msg_tuple.
      clear.
      elim: l2 => //=.
      case => [n m] => /=.
      move => l IH.
      by rewrite serialize_deserialize_id_nil IH.
    by rewrite H_eq H_eq'.
  - move => me inp st out st' ps H_eq H_eq'.
    rewrite /input_handlers /= /serialized_input_handlers /= in H_eq'.
    rewrite /pt_map_msg /= in H_eq.
    move: H_eq H_eq'.
    case H_eq_m: (deserialize inp) => [i|] H_eq H_eq'; first by repeat break_let.
    by find_injection.
  Qed.

  Lemma pt_map_trace_filterMap : 
    forall tr, pt_map_trace tr = filterMap deserialize_tr_entry tr.
  Proof.
  rewrite /pt_map_packet /tot_map_name /= /deserialize_packet.
  elim => //=.
  case => n.
  case => [i|o] l IH.
  - rewrite -IH /pt_map_trace_occ /pt_map_input /= /deserialize_tr_entry /=.
    case: deserialize => //=.
    by case => i' l'.
  - rewrite -IH /pt_map_trace_occ /pt_map_outputs /= /deserialize_tr_entry /= /id /=.
    set fm := fold_right _ _ _.
    set fm' := filterMap _ _.
    suff H_eq: fm = fm' by rewrite H_eq.
    rewrite /fm /fm'.
    clear.
    elim: o => //=.
    move => a l IH.
    by rewrite -IH.
  Qed.

  Lemma pt_map_net_deserialize_net : 
    forall net, pt_map_net net = deserialize_net net.
  Proof.
  move => net.
  rewrite /deserialize_net.
  rewrite /pt_map_net /pt_map_data /= /id /= /pt_map_packets.
  set fm := fold_right _ _ _.
  set fm' := filterMap _ _.
  suff H_eq: fm = fm' by rewrite H_eq.
  rewrite /fm /fm'.
  clear.
  rewrite /pt_map_packet /tot_map_name /= /deserialize_packet.
  elim (nwPackets net) => //=.
  case => [src dst body] /= l IH.
  rewrite IH.
  case (deserialize body) => //.
  by case => [m lb].
  Qed.

  Lemma step_async_deserialized_simulation :
  forall net net' tr,
    @step_async _ serialized_multi_params net net' tr ->
    @step_async _ orig_multi_params (deserialize_net net) (deserialize_net net') (filterMap deserialize_tr_entry tr) \/ 
    (deserialize_net net' = deserialize_net net /\ pt_trace_remove_empty_out (filterMap deserialize_tr_entry tr) = []).
  Proof.
  move => net net' tr H_st.
  rewrite -pt_map_trace_filterMap -2!pt_map_net_deserialize_net.
  exact: step_async_pt_mapped_simulation_1.
  Qed.

  Lemma step_async_deserialized_simulation_star :
  forall net tr,
    @step_async_star _ serialized_multi_params step_async_init net tr ->
    exists tr', @step_async_star _ orig_multi_params step_async_init (deserialize_net net) tr' /\ 
     pt_trace_remove_empty_out (filterMap deserialize_tr_entry tr) = pt_trace_remove_empty_out tr'.
  Proof.
  move => net tr H_st.
  apply step_async_pt_mapped_simulation_star_1 in H_st.
  break_exists.
  break_and.
  exists x.
  by rewrite -pt_map_trace_filterMap -pt_map_net_deserialize_net.
  Qed.

  Lemma step_failure_deserialized_simulation :
  forall net net' failed failed' tr,
    @step_failure _ _ serialized_failure_params (failed, net) (failed', net') tr ->
    @step_failure _ _ orig_failure_params (failed, deserialize_net net) (failed', deserialize_net net') (filterMap deserialize_tr_entry tr) \/ 
    (deserialize_net net' = deserialize_net net /\ failed = failed' /\ pt_trace_remove_empty_out (filterMap deserialize_tr_entry tr) = []).
  Proof.
  move => net net' failed failed' tr H_st.
  rewrite -pt_map_trace_filterMap -2!pt_map_net_deserialize_net.
  have H_eq_n: failed = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n.
  have H_eq_n': failed' = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed' by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n'.
  exact: step_failure_pt_mapped_simulation_1.
  Qed.

  Lemma step_failure_deserialized_simulation_star :
  forall net failed tr,
    @step_failure_star _ _ serialized_failure_params step_failure_init (failed, net) tr ->
    exists tr', @step_failure_star _ _ orig_failure_params step_failure_init (failed, deserialize_net net) tr' /\ 
     pt_trace_remove_empty_out (filterMap deserialize_tr_entry tr) = pt_trace_remove_empty_out tr'.
  Proof.
  move => net failed tr H_st.
  apply step_failure_pt_mapped_simulation_star_1 in H_st.
  break_exists.
  break_and.
  exists x.
  rewrite -pt_map_trace_filterMap -pt_map_net_deserialize_net.
  have H_eq_n: failed = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  by rewrite {1}H_eq_n.
  Qed.

  Lemma step_ordered_failure_deserialized_simulation :
    forall net net' failed failed' tr,
      @step_ordered_failure _ _ serialized_name_overlay_params serialized_fail_msg_params (failed, net) (failed', net') tr ->
      @step_ordered_failure _ _ orig_name_overlay_params orig_fail_msg_params (failed, pt_map_onet net) (failed', pt_map_onet net') (pt_map_traces tr) \/
      pt_map_onet net = pt_map_onet net' /\ failed = failed' /\ pt_map_traces tr = [].
  Proof.
  move => net net' failed failed' tr H_st.
  eapply step_ordered_failure_pt_mapped_simulation_1 in H_st.
  case: H_st => H_st; last by right; break_and.
  have H_eq_n: failed = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n.
  have H_eq_n': failed' = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed' by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n'.
  left.
  exact: H_st.
  Qed.

  Lemma step_ordered_failure_serialized_simulation_star :
    forall net failed tr,
    @step_ordered_failure_star _ _ serialized_name_overlay_params serialized_fail_msg_params step_ordered_failure_init (failed, net) tr ->
    @step_ordered_failure_star _ _ orig_name_overlay_params orig_fail_msg_params step_ordered_failure_init (failed, pt_map_onet net) (pt_map_traces tr).
  Proof.
  move => onet failed tr H_st.
  apply step_ordered_failure_pt_mapped_simulation_star_1 in H_st.
  by rewrite map_id in H_st.
  Qed.

  Lemma step_ordered_dynamic_failure_deserialized_simulation :
  forall net net' failed failed' tr,
    NoDup (odnwNodes net) ->
    @step_ordered_dynamic_failure _ _ serialized_name_overlay_params serialized_new_msg_params serialized_fail_msg_params (failed, net) (failed', net') tr ->
    @step_ordered_dynamic_failure _ _ orig_name_overlay_params orig_new_msg_params orig_fail_msg_params (failed, pt_map_odnet net) (failed', pt_map_odnet net') (pt_map_traces tr) \/
    pt_map_odnet net = pt_map_odnet net' /\ failed = failed' /\ pt_map_traces tr = [].
  Proof.
  move => net net' failed failed' tr H_nd H_st.
  eapply step_ordered_dynamic_failure_pt_mapped_simulation_1 in H_st; last by [].
  case: H_st => H_st; last by right; break_and.
  have H_eq_n: failed = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n.
  have H_eq_n': failed' = map (@tot_map_name _ _ _ _ multi_params_orig_name_tot_map) failed' by rewrite /tot_map_name /= map_id.
  rewrite {1}H_eq_n'.
  left.
  exact: H_st.
  Qed.

  Theorem step_ordered_dynamic_failure_dserialized_simulation_star :
    forall net failed tr,
    @step_ordered_dynamic_failure_star _ _ serialized_name_overlay_params serialized_new_msg_params serialized_fail_msg_params step_ordered_dynamic_failure_init (failed, net) tr ->
    @step_ordered_dynamic_failure_star _ _ orig_name_overlay_params orig_new_msg_params orig_fail_msg_params step_ordered_dynamic_failure_init (failed, pt_map_odnet net) (pt_map_traces tr).
  Proof.
  move => onet failed tr H_st.
  apply step_ordered_dynamic_failure_pt_mapped_simulation_star_1 in H_st.
  by rewrite map_id in H_st.
  Qed.

End SerializedCorrect.
