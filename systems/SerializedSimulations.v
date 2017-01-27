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

End SerializedCorrect.
