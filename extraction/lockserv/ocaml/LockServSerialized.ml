type __ = Obj.t

(** val bool_dec : bool -> bool -> bool **)

let bool_dec b1 b2 =
  if b1 then if b2 then true else false else if b2 then false else true

(** val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eq_dec eq_dec l l' =
  match l with
  | [] ->
    (match l' with
     | [] -> true
     | _ :: _ -> false)
  | y :: l0 ->
    (match l' with
     | [] -> false
     | a0 :: l1 -> if eq_dec y a0 then list_eq_dec eq_dec l0 l1 else false)

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    [])
    (fun len0 ->
    start :: (seq (Pervasives.succ start) len0))
    len

(** val null : 'a1 list -> bool **)

let null = function
| [] -> true
| _ :: _ -> false

type baseParams =
| Build_BaseParams

type data = __

type input = __

type output = __

type multiParams = { msg_eq_dec : (__ -> __ -> bool);
                     name_eq_dec : (__ -> __ -> bool); nodes : __ list;
                     init_handlers : (__ -> data);
                     net_handlers : (__ -> __ -> __ -> data -> (output
                                    list * data) * (__ * __) list);
                     input_handlers : (__ -> input -> data -> (output
                                      list * data) * (__ * __) list) }

type name = __

type msg = __

(** val name_eq_dec : baseParams -> multiParams -> name -> name -> bool **)

let name_eq_dec _ x = x.name_eq_dec

(** val nodes : baseParams -> multiParams -> name list **)

let nodes _ x = x.nodes

(** val init_handlers : baseParams -> multiParams -> name -> data **)

let init_handlers _ x = x.init_handlers

(** val net_handlers :
    baseParams -> multiParams -> name -> name -> msg -> data -> (output
    list * data) * (name * msg) list **)

let net_handlers _ x = x.net_handlers

(** val input_handlers :
    baseParams -> multiParams -> name -> input -> data -> (output
    list * data) * (name * msg) list **)

let input_handlers _ x = x.input_handlers

type ('w, 's, 'o, 'a) genHandler = 's -> (('a * 'o list) * 's) * 'w list

(** val ret : 'a4 -> ('a1, 'a2, 'a3, 'a4) genHandler **)

let ret a s =
  (((a, []), s), [])

(** val bind :
    ('a1, 'a2, 'a3, 'a4) genHandler -> ('a4 -> ('a1, 'a2, 'a3, 'a5)
    genHandler) -> ('a1, 'a2, 'a3, 'a5) genHandler **)

let bind m f s =
  let (p, ws1) = m s in
  let (p0, s') = p in
  let (a, os1) = p0 in
  let (p1, ws2) = f a s' in
  let (p2, s'') = p1 in
  let (b, os2) = p2 in
  (((b, (List.append os1 os2)), s''), (List.append ws1 ws2))

(** val send : 'a1 -> ('a1, 'a2, 'a3, unit) genHandler **)

let send w s =
  ((((), []), s), (w :: []))

(** val write_output : 'a3 -> ('a1, 'a2, 'a3, unit) genHandler **)

let write_output o s =
  ((((), (o :: [])), s), [])

(** val put : 'a2 -> ('a1, 'a2, 'a3, unit) genHandler **)

let put s _ =
  ((((), []), s), [])

(** val get : ('a1, 'a2, 'a3, 'a2) genHandler **)

let get s =
  (((s, []), s), [])

(** val runGenHandler_ignore :
    'a2 -> ('a1, 'a2, 'a3, 'a4) genHandler -> ('a3 list * 'a2) * 'a1 list **)

let runGenHandler_ignore s h =
  let (p, ms) = h s in let (p0, s') = p in let (_, os) = p0 in ((os, s'), ms)

(** val nop : ('a1, 'a2, 'a3, unit) genHandler **)

let nop x =
  ret () x

(** val when0 :
    bool -> ('a1, 'a2, 'a3, 'a4) genHandler -> ('a1, 'a2, 'a3, unit)
    genHandler **)

let when0 b m =
  if b then bind m (fun _ -> ret ()) else nop

type client_index = int

type name0 =
| Client of client_index
| Server

(** val list_Clients : int -> name0 list **)

let list_Clients num_Clients =
  List.map (fun x -> Client x) ((fun n -> (Obj.magic (seq 0 n))) num_Clients)

(** val name_eq_dec0 : int -> name0 -> name0 -> bool **)

let name_eq_dec0 num_Clients a b =
  match a with
  | Client x ->
    (match b with
     | Client c0 -> (fun _ -> (=)) num_Clients x c0
     | Server -> false)
  | Server ->
    (match b with
     | Client _ -> false
     | Server -> true)

type msg0 =
| Lock
| Unlock
| Locked

(** val msg_eq_dec0 : msg0 -> msg0 -> bool **)

let msg_eq_dec0 a b =
  match a with
  | Lock ->
    (match b with
     | Lock -> true
     | _ -> false)
  | Unlock ->
    (match b with
     | Unlock -> true
     | _ -> false)
  | Locked ->
    (match b with
     | Locked -> true
     | _ -> false)

type output0 = msg0

type data0 = { queue : client_index list; held : bool }

(** val queue : int -> data0 -> client_index list **)

let queue _ x = x.queue

(** val held : int -> data0 -> bool **)

let held _ x = x.held

(** val init_data : int -> name0 -> data0 **)

let init_data _ _ =
  { queue = []; held = false }

type 's handler = (name0 * msg0, 's, output0, unit) genHandler

(** val clientNetHandler : int -> client_index -> msg0 -> data0 handler **)

let clientNetHandler _ _ = function
| Locked ->
  bind (put { queue = []; held = true }) (fun _ -> write_output Locked)
| _ -> nop

(** val clientIOHandler : int -> client_index -> msg0 -> data0 handler **)

let clientIOHandler _ _ = function
| Lock -> send (Server, Lock)
| Unlock ->
  bind get (fun data1 ->
    when0 data1.held
      (bind (put { queue = []; held = false }) (fun _ ->
        send (Server, Unlock))))
| Locked -> nop

(** val serverNetHandler : int -> name0 -> msg0 -> data0 handler **)

let serverNetHandler _ src m =
  bind get (fun st ->
    let q = st.queue in
    (match m with
     | Lock ->
       (match src with
        | Client c ->
          bind (when0 (null q) (send (src, Locked))) (fun _ ->
            put { queue = (List.append q (c :: [])); held = st.held })
        | Server -> nop)
     | Unlock ->
       (match q with
        | [] -> put { queue = []; held = st.held }
        | _ :: l ->
          (match l with
           | [] -> put { queue = []; held = st.held }
           | x :: xs ->
             bind (put { queue = (x :: xs); held = st.held }) (fun _ ->
               send ((Client x), Locked))))
     | Locked -> nop))

(** val serverIOHandler : int -> msg0 -> data0 handler **)

let serverIOHandler _ _ =
  nop

(** val netHandler : int -> name0 -> name0 -> msg0 -> data0 handler **)

let netHandler num_Clients nm src m =
  match nm with
  | Client c -> clientNetHandler num_Clients c m
  | Server -> serverNetHandler num_Clients src m

(** val inputHandler : int -> name0 -> msg0 -> data0 handler **)

let inputHandler num_Clients nm m =
  match nm with
  | Client c -> clientIOHandler num_Clients c m
  | Server -> serverIOHandler num_Clients m

(** val nodes0 : int -> name0 list **)

let nodes0 num_Clients =
  Server :: (list_Clients num_Clients)

(** val lockServ_BaseParams : int -> baseParams **)

let lockServ_BaseParams _ =
  Build_BaseParams

(** val lockServ_MultiParams : int -> multiParams **)

let lockServ_MultiParams num_Clients =
  { msg_eq_dec = (Obj.magic msg_eq_dec0); name_eq_dec =
    (Obj.magic name_eq_dec0 num_Clients); nodes =
    (Obj.magic nodes0 num_Clients); init_handlers =
    (Obj.magic init_data num_Clients); net_handlers = (fun dst src msg1 s ->
    runGenHandler_ignore s (Obj.magic netHandler num_Clients dst src msg1));
    input_handlers = (fun nm msg1 s ->
    runGenHandler_ignore s (Obj.magic inputHandler num_Clients nm msg1)) }

type 'a serializer = { serialize : ('a -> bool list);
                       deserialize : (bool list -> ('a * bool list) option) }

(** val serialize : 'a1 serializer -> 'a1 -> bool list **)

let serialize x = x.serialize

(** val deserialize :
    'a1 serializer -> bool list -> ('a1 * bool list) option **)

let deserialize x = x.deserialize

type 'a deserializer = bool list -> ('a * bool list) option

(** val ret0 : 'a1 -> 'a1 deserializer **)

let ret0 a s =
  Some (a, s)

(** val bind0 :
    'a1 deserializer -> ('a1 -> 'a2 deserializer) -> 'a2 deserializer **)

let bind0 m f s =
  match m s with
  | Some p -> let (a, s') = p in f a s'
  | None -> None

(** val get0 : bool list deserializer **)

let get0 s =
  Some (s, s)

(** val put0 : bool list -> unit deserializer **)

let put0 s _ =
  Some ((), s)

(** val fail : 'a1 deserializer **)

let fail _ =
  None

(** val serialize_name_msg_tuple :
    baseParams -> multiParams -> msg serializer -> (name * msg) ->
    name * bool list **)

let serialize_name_msg_tuple _ _ orig_msg_serializer = function
| (n, msg1) -> (n, (orig_msg_serializer.serialize msg1))

(** val serialize_handler_result :
    baseParams -> multiParams -> output serializer -> msg serializer ->
    ((output list * data) * (name * msg) list) -> (bool list
    list * data) * (name * bool list) list **)

let serialize_handler_result orig_base_params orig_multi_params orig_output_serializer orig_msg_serializer = function
| (p, messages) ->
  let (outputs, data1) = p in
  let outputsBits = List.map orig_output_serializer.serialize outputs in
  let messagesBits =
    List.map
      (serialize_name_msg_tuple orig_base_params orig_multi_params
        orig_msg_serializer) messages
  in
  ((outputsBits, data1), messagesBits)

(** val serialized_net_handlers :
    baseParams -> multiParams -> output serializer -> msg serializer -> name
    -> name -> bool list -> data -> (bool list list * data) * (name * bool
    list) list **)

let serialized_net_handlers orig_base_params orig_multi_params orig_output_serializer orig_msg_serializer dst src mBits d =
  match orig_msg_serializer.deserialize mBits with
  | Some p ->
    let (m, _) = p in
    serialize_handler_result orig_base_params orig_multi_params
      orig_output_serializer orig_msg_serializer
      (orig_multi_params.net_handlers dst src m d)
  | None -> (([], d), [])

(** val serialized_input_handlers :
    baseParams -> multiParams -> input serializer -> output serializer -> msg
    serializer -> name -> bool list -> data -> (bool list
    list * data) * (name * bool list) list **)

let serialized_input_handlers orig_base_params orig_multi_params orig_input_serializer orig_output_serializer orig_msg_serializer h inpBits d =
  match orig_input_serializer.deserialize inpBits with
  | Some p ->
    let (inp, _) = p in
    serialize_handler_result orig_base_params orig_multi_params
      orig_output_serializer orig_msg_serializer
      (orig_multi_params.input_handlers h inp d)
  | None -> (([], d), [])

(** val serialized_base_params : baseParams -> baseParams **)

let serialized_base_params _ =
  Build_BaseParams

(** val serialized_multi_params :
    baseParams -> multiParams -> input serializer -> output serializer -> msg
    serializer -> multiParams **)

let serialized_multi_params orig_base_params orig_multi_params orig_input_serializer orig_output_serializer orig_msg_serializer =
  { msg_eq_dec = (Obj.magic list_eq_dec bool_dec); name_eq_dec =
    orig_multi_params.name_eq_dec; nodes = orig_multi_params.nodes;
    init_handlers = orig_multi_params.init_handlers; net_handlers =
    (Obj.magic serialized_net_handlers orig_base_params orig_multi_params
      orig_output_serializer orig_msg_serializer); input_handlers =
    (Obj.magic serialized_input_handlers orig_base_params orig_multi_params
      orig_input_serializer orig_output_serializer orig_msg_serializer) }

(** val msg_serialize : msg0 -> bool list **)

let msg_serialize = function
| Lock -> true :: []
| Unlock -> false :: (true :: [])
| Locked -> false :: (false :: [])

(** val msg_deserialize : msg0 deserializer **)

let msg_deserialize =
  bind0 get0 (fun l ->
    match l with
    | [] -> fail
    | b :: l' ->
      if b
      then bind0 (put0 l') (fun _ -> ret0 Lock)
      else (match l' with
            | [] -> fail
            | b0 :: l'' ->
              if b0
              then bind0 (put0 l'') (fun _ -> ret0 Unlock)
              else bind0 (put0 l'') (fun _ -> ret0 Locked)))

(** val msg_Serializer : msg0 serializer **)

let msg_Serializer =
  { serialize = msg_serialize; deserialize = msg_deserialize }

(** val transformed_base_params : int -> baseParams **)

let transformed_base_params num_Clients =
  serialized_base_params (lockServ_BaseParams num_Clients)

(** val transformed_multi_params : int -> multiParams **)

let transformed_multi_params num_Clients =
  serialized_multi_params (lockServ_BaseParams num_Clients)
    (lockServ_MultiParams num_Clients) (Obj.magic msg_Serializer)
    (Obj.magic msg_Serializer) (Obj.magic msg_Serializer)
