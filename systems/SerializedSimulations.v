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
  Context {orig_data_serializer : Serializer data}.
  Context {orig_input_serializer : Serializer input}.
  Context {orig_output_serializer : Serializer output}.
  Context {orig_msg_serializer : Serializer msg}.

  Instance orig_multi_params_name_tot_map :
    MultiParamsNameTotalMap orig_multi_params multi_params :=
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
    BaseParamsTotalMap orig_base_params base_params :=
  {
    tot_map_data := serialize;
    tot_map_input := serialize;
    tot_map_output := serialize
  }.

  Instance orig_multi_params_tot_msg_map :
    MultiParamsMsgTotalMap orig_multi_params multi_params :=
  {
    tot_map_msg := serialize
  }.

  Instance refined_multi_params_map_congruency :
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
    rewrite 2!serialize_deserialize_id_nil.
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
    rewrite 2!serialize_deserialize_id_nil.
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

  Definition serialize_packet p :=
    @mkPacket _ multi_params
              (@pSrc _ orig_multi_params p)
              (pDst p)
              (serialize (pBody p)).

  Definition serialize_net (net : @network _ orig_multi_params) : (@network _ multi_params) :=
    @mkNetwork _ multi_params (map serialize_packet (nwPackets net)) (fun n => serialize (net.(nwState) n)).

  Definition serialize_tr_entry (e : @name _ orig_multi_params * (@input orig_base_params + list (@output orig_base_params))) : 
  @name _ multi_params * (@input base_params + list (@output base_params)) := 
  let (n, s) := e in
  match s with
  | inl io => (n, inl (serialize io))
  | inr lo => (n, inr (map serialize lo))
  end.

  Theorem step_async_serialize_simulation_1 :
    forall net net' tr,
      @step_async _ orig_multi_params net net' tr ->
      @step_async _ multi_params (serialize_net net) (serialize_net net') (map serialize_tr_entry tr).
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

  Lemma step_async_serialize_simulation_star_1 :
    forall net tr,
      @step_async_star _ orig_multi_params step_async_init net tr ->
      @step_async_star _ multi_params step_async_init (serialize_net net) (map serialize_tr_entry tr).
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

  Definition deserialize_packet (p : @packet _ multi_params) : option (@packet _ orig_multi_params) :=
    match (deserialize (pBody p)) with
    | None => None
    | Some (body, _) =>
      Some (@mkPacket _ orig_multi_params (pSrc p) (pDst p) body)
    end.

  Definition deserialize_net (net: @network _ multi_params) :  (@network _ orig_multi_params) :=
    mkNetwork
      (filterMap deserialize_packet (nwPackets net))
      (fun h => match (deserialize (nwState net h)) with
               | Some (data, _) => data
               | None => init_handlers h
               end).

  Definition deserialize_tr_entry (e : @name _ multi_params * (@input base_params + list (@output base_params))) :
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

  Lemma step_async_serialized_simulation_2 :
    forall net net' tr unet,
      @step_async _ multi_params net net' tr ->
      serialize_net unet = net ->
      exists unet' utr,
        @step_async _  orig_multi_params unet unet' utr /\
        serialize_net unet' = net' /\
        map serialize_tr_entry utr = tr.
  Proof.
  Admitted.

  Lemma step_async_serialize_ex_simulation_star :
    forall net tr,
      @step_async_star _ multi_params step_async_init net tr ->
      exists unet utr, 
        @step_async_star _ orig_multi_params step_async_init unet utr /\
        serialize_net unet = net /\
        map serialize_tr_entry utr = tr.
  Proof.
  move => net tr H_step.
  remember step_async_init as y in *.
  move: Heqy.
  induction H_step using refl_trans_1n_trace_n1_ind => H_init /=.
    rewrite H_init /step_async_init /= /tot_map_net /=.
    exists {| nwPackets := []; nwState := init_handlers |}.
    exists [].
    by split; first exact: RT1nTBase.
  concludes.
  repeat find_rewrite.
  break_exists.
  break_and.
  have H_star := step_async_serialized_simulation_2 _ _ _ _ H H1.
  break_exists.
  break_and.
  exists x2.
  exists (x1 ++ x3).
  split.
    apply: (refl_trans_1n_trace_trans H0).
    rewrite (app_nil_end x3).
    apply: (@RT1nTStep _ _ _ _ x2) => //.
    exact: RT1nTBase.
  split => //.
  rewrite map_app.
  by rewrite H2 H5.  
  Qed.

  Lemma deserialize_serialize_net_id : forall net,
      deserialize_net (serialize_net net) = net.
  Proof.
  case => ps nwS.
  rewrite /deserialize_net /serialize_net /=.
  set ps' := filterMap _ _.
  set nwSf := fun _ => _.
  have H_p: ps' = ps.
    rewrite /ps'.
    clear.
    rewrite /deserialize_packet.
    elim: ps => [|p ps IH] //=.
    rewrite serialize_deserialize_id_nil IH.
    by case: p.
  have H_s: nwSf = nwS.
    rewrite /nwSf.
    apply functional_extensionality.
    move => n.
    by rewrite serialize_deserialize_id_nil.
  by rewrite H_p H_s.
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

End SerializedCorrect.
