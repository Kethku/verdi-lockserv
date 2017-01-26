Require Import StructTact.Util.
Require Import Verdi.Verdi.
Require Import FunctionalExtensionality.
Require Import Serialized.
Require Import Cheerios.Core.

Section SerializedCorrect.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {orig_data_serializer : Serializer data}.
  Context {orig_input_serializer : Serializer input}.
  Context {orig_output_serializer : Serializer output}.
  Context {orig_msg_serializer : Serializer msg}.

  Definition orig_packet := @packet _ orig_multi_params.
  Definition orig_network := @network _ orig_multi_params.
  Definition serialized_packet := @packet _ multi_params.
  Definition serialized_network := @network _ multi_params.

  Definition revertPacket (p : serialized_packet) : option orig_packet :=
    match (deserialize (pBody p)) with
    | None => None
    | Some (body, rest) =>
      Some (@mkPacket _ orig_multi_params (pSrc p) (pDst p) body)
    end.

  Definition revertNetwork (net: serialized_network) : orig_network :=
    mkNetwork
      (filterMap revertPacket (nwPackets net))
      (fun h => match (deserialize (nwState net h)) with
             | Some (data, rest) => data
             | None => init_handlers h
             end).

  Lemma Serialize_deserialize_init_handlers:
    (fun h : name => match deserialize (serialize (init_handlers h)) with
                 | Some (data, _) => data
                 | None => init_handlers h
                  end) = init_handlers.
  Proof.
    rewrite <- functional_extensionality with (f := (fun h : name => match deserialize (serialize (init_handlers h)) with
                                                                 | Some (data, _) => data
                                                                 | None => init_handlers h
                                                                 end)); auto.
    intros.
    Admitted.
    (* rewrite serialize_reversible with (x := (init_handlers x)). *)
    (* auto. *)
  (* Qed. *)

  Definition all_packets_deserialize (net : serialized_network) :=
    forall p,
      In p (nwPackets net) ->
      exists m,
        deserialize (pBody p) = Some (m, []).

  (* Lemma all_packets_deserialize_inv : *)
  (*   forall net, *)
  (*     reachable step_m step_m_init net -> *)
  (*     all_packets_deserialize net. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold reachable in *. *)
  (*   destruct H. *)
  (*   inversion H. *)
  (*   - subst. *)
  (*     unfold step_m_init. *)
  (*     unfold init_handlers. *)
  (*     unfold all_packets_deserialize. *)

  (* Admitted. *)
      

  (* Lemma reachable_revert_step : *)
  (*   forall state new_state output, *)
  (*     reachable step_d step_m_init state -> *)
  (*     step_d state new_state output -> *)
  (*     (exists out, step_m (revertNetwork state) (revertNetwork new_state) output) *)
  (*     \/ revertNetwork state = revertNetwork newstate. *)
  (* Proof. *)
  (*   intros. *)
  (*   match goal with H : step_d _ _ _ |- _ => invcs H end. *)
  (*   - unfold serialized_net_handlers in *. *)


  (* Admitted. *)

  (* Theorem reachable_revert : *)
  (*   true_in_reachable step_d step_m_init *)
  (*                     (fun st => *)
  (*                        reachable step_m step_m_init (revertNetwork st)). *)
  (* Proof. *)
  (*   apply true_in_reachable_reqs. *)
  (*   - unfold revertNetwork. simpl. *)
  (*     unfold reachable. *)
  (*     unfold serialized_init_handlers. *)
  (*     rewrite Serialize_deserialize_init_handlers. *)
  (*     exists []. *)
  (*     constructor. *)
  (*   - intros. *)
  (*     find_apply_lem_hyp reachable_revert_step; auto. *)
  (*     intuition. *)
  (*     + unfold reachable in *. *)
  (*       break_exists. *)
  (*       eexists. *)
  (*       apply refl_trans_n1_1n_trace. *)
  (*       econstructor; eauto using refl_trans_1n_n1_trace. *)
  (*     + find_rewrite. auto. *)
  (* Qed. *)

  (* Theorem true_in_reachable_transform : *)
  (*   forall P, *)
  (*     true_in_reachable step_m step_m_init P -> *)
  (*     true_in_reachable step_d step_m_init (fun net => P (revertNetwork net)). *)
  (* Proof. *)
  (*   intros. find_apply_lem_hyp true_in_reachable_elim. intuition. *)
  (*   apply true_in_reachable_reqs. *)
  (*   - unfold step_m_init in *. *)
  (*     unfold revertNetwork. *)
  (*     simpl. *)
  (*     unfold serialized_init_handlers. *)
  (*     rewrite Serialize_deserialize_init_handlers. *)
  (*     assumption. *)
  (*   - intros. find_copy_apply_lem_hyp reachable_revert. *)
  (*     find_apply_lem_hyp reachable_revert_step; auto. *)
  (*     intuition. *)
  (*     + break_exists. eauto. *)
  (*     + repeat find_rewrite. auto. *)
  (* Qed. *)

End SerializedCorrect.
