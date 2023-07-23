import Mathlib.Init.Data.List.Instances

instance [Pure m] : MonadLift Id m where
  monadLift x := pure x

instance : MonadLift Option List where
  monadLift x := x.toList

class ConsM (m : Type u → Type u) (L : Type u) (α : Type u) where
  nilM : m L
  consM : α → L → m L

export ConsM (nilM)

instance [MonadLift n m] [ConsM n L α] : ConsM m L α where
  nilM := show m L from (ConsM.nilM α : n L)
  consM a l := show m L from (ConsM.consM a l : n L)

class UnconsM (m : Type u → Type u) (L : Type u) (α : outParam (Type u)) extends ConsM m L α where
  unconsM : L → m (Option (α × L))

export UnconsM (unconsM)

instance [MonadLift n m] [UnconsM n L α] : UnconsM m L α where
  unconsM l := show m (Option (α × L)) from (UnconsM.unconsM l : n _)

private local instance [Monad n] : Inhabited (δ → (α → δ → n (ForInStep δ)) → n δ) where
  default d _ := pure d in

/-- The implementation of `ForIn`, which enables `for a in L do ...` notation. -/
@[specialize] protected partial def Uncons.forIn [Monad m] [Monad n] [MonadLiftT m n]
    [UnconsM m L α] (as : L) (init : δ) (f : α → δ → n (ForInStep δ)) : n δ := do
  match ← (unconsM as : m _) with
  | none => pure init
  | some (a, t) => match (← f a init) with
      | ForInStep.done d  => pure d
      | ForInStep.yield d => Uncons.forIn (m := m) t d f

instance [Monad m] [UnconsM m L α] : ForIn m L α where
  forIn := Uncons.forIn (m := m) (n := m)

instance [Pure m] : UnconsM m (List α) α where
  nilM := pure []
  consM a l := pure (a :: l)
  unconsM := fun
  | [] => pure none
  | h :: t => pure (some (h, t))

class SquashM (m : Type u → Type u) (L : Type u) (α : outParam (Type u)) extends UnconsM m L α where
  squashM : m L → L

instance [Pure n] [MonadLiftT n List] : SquashM n (List α) α where
  squashM l := (show List (List α) from l).join

export SquashM (squashM)

def consM [Monad m] [SquashM m L α] (x : m (Option α × L)) : L :=
  squashM do match ← x with
    | (none, xs) => pure xs
    | (some x, xs) => ConsM.consM x xs

private local instance : Inhabited ((L : Type u) → (I : SquashM.{u} m L a) → (α → m α) → α → L) :=
  ⟨fun L I _ _ => squashM ((I.toUnconsM.toConsM.nilM) : m L)⟩

/-- Construct a `ListM` recursively. Failures from `f` will result in `uncons` failing.  -/
partial def fix [Monad m] (L : Type _) [SquashM m L α] (f : α → m α) (x : α) : L :=
  consM do pure (some x, ← fix L f <$> f x)

example (f : α → List α) (a : α) : List α := fix (List α) f a

#eval fix (List Nat) (fun n => List.range n) 5 -- okay...?
