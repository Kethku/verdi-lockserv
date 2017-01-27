Require Import Verdi.Verdi.
Require Import Cheerios.Core.

Set Implicit Arguments.

Section Serialized.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {orig_input_serializer : Serializer input}.
  Context {orig_output_serializer : Serializer output}.
  Context {orig_msg_serializer : Serializer msg}.

  Definition serialize_name_msg_tuple (n_msg : (name * msg)) :=
    let (n, msg) := n_msg in
    (n, serialize msg).

  Definition serialize_handler_result (result : (list output) * data * list (name * msg)) :
    list (list bool) * data * list (name * list bool) :=
    let '(outputs, data, messages) := result in
    let outputsBits := map (@serialize output orig_output_serializer) outputs in
    let messagesBits := map serialize_name_msg_tuple messages in
    (outputsBits, data, messagesBits).

  Definition serialized_net_handlers
             (dst : name)
             (src : name)
             (mBits : list bool)
             (d : data) :
    list (list bool) * data * list (name * list bool) :=
    match (deserialize mBits) with
    | None => ([], d, [])
    | Some (m, rest) =>
      serialize_handler_result (net_handlers dst src m d)
    end.

  Definition serialized_input_handlers
             (h : name)
             (inpBits : list bool)
             (d : data) :
    list (list bool) * data * list (name * list bool) :=
    match (deserialize inpBits) with
    | None => ([], d, [])
    | Some (inp, rest) =>
      serialize_handler_result (input_handlers h inp d)
    end.

  Instance base_params : BaseParams :=
    {
      data := data;
      input := list bool;
      output := list bool
    }.

  Instance multi_params : MultiParams _ :=
    {
      name := name;
      name_eq_dec := name_eq_dec;
      msg := list bool;
      msg_eq_dec := (list_eq_dec Bool.bool_dec);
      nodes := nodes;
      init_handlers := init_handlers;
      net_handlers := serialized_net_handlers;
      input_handlers := serialized_input_handlers;
    }.
  Proof.
    - eauto using all_names_nodes.
    - eauto using no_dup_nodes.
  Defined.
End Serialized.

Hint Extern 5 (@BaseParams) => apply base_params : typeclass_instances.
Hint Extern 5 (@MultiParams _) => apply multi_params : typeclass_instances.
