type __ = Obj.t

val bool_dec : bool -> bool -> bool

val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val seq : int -> int -> int list

val null : 'a1 list -> bool

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

val name_eq_dec : baseParams -> multiParams -> name -> name -> bool

val nodes : baseParams -> multiParams -> name list

val init_handlers : baseParams -> multiParams -> name -> data

val net_handlers :
  baseParams -> multiParams -> name -> name -> msg -> data -> (output
  list * data) * (name * msg) list

val input_handlers :
  baseParams -> multiParams -> name -> input -> data -> (output
  list * data) * (name * msg) list

type ('w, 's, 'o, 'a) genHandler = 's -> (('a * 'o list) * 's) * 'w list

val ret : 'a4 -> ('a1, 'a2, 'a3, 'a4) genHandler

val bind :
  ('a1, 'a2, 'a3, 'a4) genHandler -> ('a4 -> ('a1, 'a2, 'a3, 'a5) genHandler)
  -> ('a1, 'a2, 'a3, 'a5) genHandler

val send : 'a1 -> ('a1, 'a2, 'a3, unit) genHandler

val write_output : 'a3 -> ('a1, 'a2, 'a3, unit) genHandler

val put : 'a2 -> ('a1, 'a2, 'a3, unit) genHandler

val get : ('a1, 'a2, 'a3, 'a2) genHandler

val runGenHandler_ignore :
  'a2 -> ('a1, 'a2, 'a3, 'a4) genHandler -> ('a3 list * 'a2) * 'a1 list

val nop : ('a1, 'a2, 'a3, unit) genHandler

val when0 :
  bool -> ('a1, 'a2, 'a3, 'a4) genHandler -> ('a1, 'a2, 'a3, unit) genHandler

type client_index = int

type name0 =
| Client of client_index
| Server

val list_Clients : int -> name0 list

val name_eq_dec0 : int -> name0 -> name0 -> bool

type msg0 =
| Lock
| Unlock
| Locked

val msg_eq_dec0 : msg0 -> msg0 -> bool

type output0 = msg0

type data0 = { queue : client_index list; held : bool }

val queue : int -> data0 -> client_index list

val held : int -> data0 -> bool

val init_data : int -> name0 -> data0

type 's handler = (name0 * msg0, 's, output0, unit) genHandler

val clientNetHandler : int -> client_index -> msg0 -> data0 handler

val clientIOHandler : int -> client_index -> msg0 -> data0 handler

val serverNetHandler : int -> name0 -> msg0 -> data0 handler

val serverIOHandler : int -> msg0 -> data0 handler

val netHandler : int -> name0 -> name0 -> msg0 -> data0 handler

val inputHandler : int -> name0 -> msg0 -> data0 handler

val nodes0 : int -> name0 list

val lockServ_BaseParams : int -> baseParams

val lockServ_MultiParams : int -> multiParams

type 'a serializer = { serialize : ('a -> bool list);
                       deserialize : (bool list -> ('a * bool list) option) }

val serialize : 'a1 serializer -> 'a1 -> bool list

val deserialize : 'a1 serializer -> bool list -> ('a1 * bool list) option

type 'a deserializer = bool list -> ('a * bool list) option

val ret0 : 'a1 -> 'a1 deserializer

val bind0 : 'a1 deserializer -> ('a1 -> 'a2 deserializer) -> 'a2 deserializer

val get0 : bool list deserializer

val put0 : bool list -> unit deserializer

val fail : 'a1 deserializer

val serialize_name_msg_tuple :
  baseParams -> multiParams -> msg serializer -> (name * msg) -> name * bool
  list

val serialize_handler_result :
  baseParams -> multiParams -> output serializer -> msg serializer ->
  ((output list * data) * (name * msg) list) -> (bool list
  list * data) * (name * bool list) list

val serialized_net_handlers :
  baseParams -> multiParams -> output serializer -> msg serializer -> name ->
  name -> bool list -> data -> (bool list list * data) * (name * bool list)
  list

val serialized_input_handlers :
  baseParams -> multiParams -> input serializer -> output serializer -> msg
  serializer -> name -> bool list -> data -> (bool list
  list * data) * (name * bool list) list

val serialized_base_params : baseParams -> baseParams

val serialized_multi_params :
  baseParams -> multiParams -> input serializer -> output serializer -> msg
  serializer -> multiParams

val msg_serialize : msg0 -> bool list

val msg_deserialize : msg0 deserializer

val msg_Serializer : msg0 serializer

val transformed_base_params : int -> baseParams

val transformed_multi_params : int -> multiParams
