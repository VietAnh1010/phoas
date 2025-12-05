open Map

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

module type ReaderT = sig
  module R : sig type t end
  module M : Monad
  type r = R.t
  type 'a t
  val reader_t : (r -> 'a M.t) -> 'a t
  val run_reader_t : 'a t -> r -> 'a M.t
end

module type StateT = sig
  module S : sig type t end
  module M : Monad
  type s = S.t
  type 'a t
  val state_t : (s -> ('a * s) M.t) -> 'a t
  val run_state_t : 'a t -> s -> ('a * s) M.t
end

module Identity = struct
  type 'a t = 'a
  let pure x = x
  let map f m = f m
  let bind m f = f m
end

module Monad_StateT (T : StateT) = struct
  open T
  let pure x = state_t (fun s -> M.pure (x, s))
  let bind m f = state_t (fun s -> M.bind (run_state_t m s) (fun (x, s) -> run_state_t (f x) s))
end

module MonadState_StateT (T : StateT) = struct
  open T
  let get = state_t (fun s -> M.pure (s, s))
  let put s = state_t (fun _ -> M.pure ((), s))
  let state f = state_t (fun s -> M.pure (f s))
end

module State (S : sig type t end) = struct
  module T = struct
    module S = S
    module M = Identity
    type s = S.t
    type 'a t = s -> ('a * s) M.t
    let state_t f = f
    let run_state_t m = m
  end

  include T
  include Monad_StateT (T)
  include MonadState_StateT (T)
end