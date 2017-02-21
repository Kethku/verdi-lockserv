open LockServ

module LockServArrangement = struct
  type name = LockServ.name
  type state = LockServ.data
  type input = LockServ.input
  type output = LockServ.output
  type msg = msg
  type client_id = int
  type res = (output list * state) * ((name * msg) list)

  let systemName : string = "Lock Server"
  let serializeName : name -> string = Serialization.serializeName (* This is where I change the serialization. Might not need shim *)
  let deserializeName : string -> name option = Serialization.deserializeName
  let init : name -> state = fun n ->
    Obj.magic (lockServ_MultiParams.init_handlers (Obj.magic n))

  let handleIO : name -> input -> state -> res =
    fun n i s ->
      Obj.magic (lockServ_MultiParams.input_handlers (Obj.magic n) (Obj.magic i) (Obj.magic s))

  let deserializeMsg : string -> msg = Serialization.deserializeMsg
  let serializeMsg : msg -> string = Serialization.serializeMsg

  let failMsg : msg option = Some Fail
  let newMsg : msg option = None
  let debug : bool = true  (* Ask about no input and output in arrangement. Maybe make shim which doesn't have this stuff? *)

