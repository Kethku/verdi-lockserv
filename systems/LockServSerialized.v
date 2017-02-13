Require Import Verdi.Verdi.
Require Import Verdi.LockServ.
Require Import Cheerios.Cheerios.
Require Import VerdiCheerios.SerializedParams.

Import DeserializerNotations.

Section LockServSerialize.
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

  Variable num_Clients : nat.

  Print SerializedParams.serialized_base_params.
  
  Definition transformed_base_params :=
    @SerializedParams.serialized_base_params (LockServ_BaseParams num_Clients).

  Definition transformed_multi_params :=
    @SerializedParams.serialized_multi_params (LockServ_BaseParams num_Clients) (LockServ_MultiParams num_Clients) Msg_Serializer Msg_Serializer Msg_Serializer.

  Definition transformed_network :=
    @network transformed_base_params transformed_multi_params.
End LockServSerialize.