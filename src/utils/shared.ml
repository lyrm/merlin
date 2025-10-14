type 'a t = { mutex : Mutex.t; cond : Condition.t; mutable value : 'a option }

let create () =
  { mutex = Mutex.create (); cond = Condition.create (); value = None }

let put_ack t a =
  Mutex.lock t.mutex;
  assert (t.value = None);
  t.value <- Some a;
  Condition.signal t.cond;
  Condition.wait t.cond t.mutex;
  Mutex.unlock t.mutex

let take t =
  Mutex.lock t.mutex;
  let rec loop () =
    match t.value with
    | None ->
      Condition.wait t.cond t.mutex;
      loop ()
    | Some v -> v
  in
  let res = loop () in
  t.value <- None;
  Condition.signal t.cond;
  Mutex.unlock t.mutex;
  res

(* let[@inline] assert_mutex_locked ?fname t =
  try
    if Mutex.try_lock t.mutex then Mutex.unlock t.mutex;
    (* Mutex was not locked *)
    let m =
      "Can only be used when the mutex is already locked"
      ^
      match fname with
      | None -> ""
      | Some f -> "(" ^ f ^ ")"
    in
    failwith m
  with Sys_error s when s = "Mutex.lock: Resource deadlock avoided" -> () *)

let unsafe_put_ack t a =
  (* assert_mutex_locked ~fname:"unsafe_put_ack" t; *)
  assert (t.value = None);
  t.value <- Some a;
  Condition.signal t.cond;
  Condition.wait t.cond t.mutex

let unsafe_take t =
  (* assert_mutex_locked ~fname:"unsafe_take" t; *)
  let rec loop () =
    match t.value with
    | None ->
      Condition.wait t.cond t.mutex;
      loop ()
    | Some v -> v
  in
  let res = loop () in
  t.value <- None;
  Condition.signal t.cond;
  res

let unsafe_get t = t.value

let wait a = Condition.wait a.cond a.mutex
let signal a = Condition.signal a.cond
let protect a = Mutex.protect a.mutex

let lock a = Mutex.lock a.mutex
let unlock a = Mutex.unlock a.mutex
