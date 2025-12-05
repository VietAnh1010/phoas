module type Monad = sig
  type 'a t
  val pure : 'a -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module type MonadReader = sig
  include Monad
  type r
  val ask : r t
  val local : (r -> r) -> 'a t -> 'a t
  val reader : (r -> 'a) -> 'a t
end

module type MonadState = sig
  include Monad
  type s
  val get : s t
  val put : s -> unit t
  val state : (s -> ('a * s)) -> 'a t
end

module Identity = struct
  type 'a t = {run : 'a}
  let pure x = {run = x}
  let map f m = {run = f m.run}
  let bind m f = f m.run
end

module ReaderT (R : sig type t end) (M : sig type 'a t end) = struct
  type r = R.t
  type 'a m = 'a M.t
  type 'a t = {run : r -> 'a m}
end

module Monad_ReaderT (R : sig type t end) (M : Monad) = struct
  open ReaderT(R)(M)
  let pure x = {run = fun _ -> M.pure x}
  let map f m = {run = fun r -> M.map f (m.run r)}
  let bind m f = {run = fun r -> M.bind (m.run r) (fun x -> (f x).run r)}
end

module MonadReader_ReaderT (R : sig type t end) (M : Monad) = struct
  open ReaderT(R)(M)
  let ask = {run = fun r -> M.pure r}
  let local f m = {run = fun r -> m.run (f r)}
  let reader f = {run = fun r -> M.pure (f r)}
end

module MonadState_ReaderT (R : sig type t end) (M : MonadState) = struct
  open ReaderT(R)(M)
  let get = {run = fun _ -> M.get}
  let put s = {run = fun _ -> M.put s}
  let state f = {run = fun _ -> M.state f}
end

module Reader (R : sig type t end) = struct
  include ReaderT(R)(Identity)
  include Monad_ReaderT(R)(Identity)
  include MonadReader_ReaderT(R)(Identity)
end

module StateT (S : sig type t end) (M : sig type 'a t end) = struct
  type s = S.t
  type 'a m = 'a M.t
  type 'a t = {run : s -> ('a * s) m}
end

module Monad_StateT (S : sig type t end) (M : Monad) = struct
  open StateT(S)(M)
  let pure x = {run = fun s -> M.pure (x, s)}
  let map f m = {run = fun s -> M.map (fun (x, s) -> (f x, s)) (m.run s)}
  let bind m f = {run = fun s -> M.bind (m.run s) (fun (x, s) -> (f x).run s)}
end

module MonadState_StateT (S : sig type t end) (M : Monad) = struct
  open StateT(S)(M)
  let get = {run = fun s -> M.pure (s, s)}
  let put s = {run = fun _ -> M.pure ((), s)}
  let state f = {run = fun s -> M.pure (f s)}
end

module MonadReader_StateT (S : sig type t end) (M : MonadReader) = struct
  open StateT(S)(M)
  let ask = {run = fun s -> M.map (fun r -> (r, s)) M.ask}
  let local f m = {run = fun s -> M.local f (m.run s)}
  let reader f = {run = fun s -> M.map (fun x -> (x, s)) (M.reader f)}
end

module State (S : sig type t end) = struct
  include StateT(S)(Identity)
  include Monad_StateT(S)(Identity)
  include MonadState_StateT(S)(Identity)
end

module M0 = State(String)
module M1 = struct
  include ReaderT(Int)(M0)
  include Monad_ReaderT(Int)(M0)
  include MonadReader_ReaderT(Int)(M0)
  include MonadState_ReaderT(Int)(M0)
end

let m : unit M1.t =
  M1.bind M1.ask @@ fun r ->
  M1.bind M1.get @@ fun s ->
  M1.put (s ^ string_of_int r)

let () =
  let (_, s) = ((m.run 1).run "Max Verstappen ").run in
  print_endline s
