Require Import Verdi.Verdi.
Require Import Verdi.LockServ.
Require Import Verdi.PartialMapSimulations.
Require Import Cheerios.Cheerios.
Require Import VerdiCheerios.SerializedParams.
Require Import VerdiCheerios.SerializedParamsCorrect.

Require Import mathcomp.ssreflect.ssreflect.

Import DeserializerNotations.

Definition Msg_serialize (msg: Msg) :=
  match msg with
  | Lock => [true]
  | Unlock => [false; true]
  | Locked => [false; false]
  end.

Definition Msg_deserialize : deserializer Msg :=
  l <- get ;;
  match l with
  | [] => fail
  | true :: l' => put l' ;; ret Lock
  | false :: l' =>
    match l' with
    | [] => fail
    | true :: l'' => put l'' ;; ret Unlock
    | false :: l'' => put l'' ;; ret Locked
    end
  end.

Lemma Msg_serialize_deserialize_id :
  serialize_deserialize_id_spec Msg_serialize Msg_deserialize.
Proof.
  unfold Msg_serialize, Msg_deserialize.
  destruct a; serialize_deserialize_id_crush.
Qed.

Instance Msg_Serializer : Serializer Msg :=
  {|
    serialize := Msg_serialize;
    deserialize := Msg_deserialize;
    serialize_deserialize_id := Msg_serialize_deserialize_id
  |}.

Section LockServSerialize.
  Variable num_Clients : nat.

  Definition transformed_base_params :=
    @SerializedParams.serialized_base_params (LockServ_BaseParams num_Clients).

  Definition transformed_multi_params :=
    @SerializedParams.serialized_multi_params (LockServ_BaseParams num_Clients) (LockServ_MultiParams num_Clients) Msg_Serializer Msg_Serializer Msg_Serializer.

  Theorem transformed_correctness :
    forall net tr,
      step_async_star (params := transformed_multi_params) step_async_init net tr ->
      @mutual_exclusion num_Clients (nwState (deserialize_net net)).
  Proof.
  move => net tr H_st.
  apply true_in_reachable_mutual_exclusion.
  have H_st' := step_async_deserialized_simulation_star _ _ H_st.
  break_exists_name tr'.
  break_and.
  by exists tr'.
  Qed.
End LockServSerialize.
