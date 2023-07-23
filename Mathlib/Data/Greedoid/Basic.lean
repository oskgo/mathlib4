import Mathlib.Data.List.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Data.List.Infix
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.List
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Tactic.TFAE
import Mathlib.Tactic.WLOG
import Mathlib.Combinatorics.SetFamily.Accessible
import Mathlib.Combinatorics.SetFamily.Bases
import Mathlib.Combinatorics.SetFamily.Language
import Mathlib.Combinatorics.SetFamily.ExchangeAxiom
import Mathlib.Data.Greedoid.Predefs

/-- Merging of language and system version of greedoid.
    This will (potentially) help `Greedoid` cover theorems written in
    both language and systems. -/
structure Greedoid (α : Type _) [Fintype α] [DecidableEq α] where
  /-- Greedoid as a language. -/
  language : GreedoidLanguage α
  /-- Greedoid as a system. -/
  system : GreedoidSystem α
  /-- `language` and `system` are related. -/
  related : Greedoid.relatedLanguageSystem language system

section Greedoid

variable {α : Type _} [DecidableEq α] [Fintype α]

/-- Definition of `Finset` in `Greedoid` -/
protected def Greedoid.finsetMem (s : Finset α) (G : Greedoid α) := s ∈ G.system.feasibleSet

/-- Definition of `List` (or equivalently, `Word`) in `Greedoid` -/
protected def Greedoid.listMem (l : List α) (G : Greedoid α) := l ∈ G.language.language

@[inherit_doc] infix:50 " ∈ₛ " => Greedoid.finsetMem
/-- Negated version of `∉ₛ` -/
infix:50 " ∉ₛ " => fun s G => ¬ (Greedoid.finsetMem s G)
@[inherit_doc] infix:50 " ∈ₗ " => Greedoid.listMem
/-- Negated version of `∉ₗ` -/
infix:50 " ∉ₗ " => fun l G => ¬ (Greedoid.listMem l G)
/-- Prefer `∈ₛ` for greedoids. -/
instance {α : Type _} [Fintype α] [DecidableEq α] :
  Membership (Finset α) (Greedoid α) := ⟨Greedoid.finsetMem⟩

end Greedoid

namespace Greedoid

variable {α : Type _} [DecidableEq α] [Fintype α] {G : Greedoid α}

open Nat List Finset GreedoidLanguage GreedoidSystem

theorem eq_of_veq : ∀ {G₁ G₂ : Greedoid α},
  G₁.language = G₂.language → G₁.system = G₂.system → G₁ = G₂
  | ⟨l₁, s₁, _⟩, ⟨l₂, s₂, _⟩, h₁, h₂ => by cases h₁; cases h₂; rfl

theorem eq_of_leq : ∀ {G₁ G₂ : Greedoid α}, G₁.language = G₂.language → G₁ = G₂ := by
  intro G₁ G₂ hl
  apply eq_of_veq hl
  rw [← relatedLanguageSystem_eq G₁.related G₂.related]
  exact hl

theorem eq_of_seq : ∀ {G₁ G₂ : Greedoid α}, G₁.system = G₂.system → G₁ = G₂ := by
  intro G₁ G₂ hs
  apply eq_of_veq _ hs
  rw [relatedLanguageSystem_eq G₁.related G₂.related]
  exact hs

theorem language_injective :
    Function.Injective (language : Greedoid α → GreedoidLanguage α) :=
  fun _ _ => eq_of_leq

theorem system_injective :
    Function.Injective (system : Greedoid α → GreedoidSystem α) :=
  fun _ _ => eq_of_seq

@[simp]
theorem language_inj {G₁ G₂ : Greedoid α} :
    G₁.language = G₂.language ↔ G₁ = G₂ :=
  language_injective.eq_iff

@[simp]
theorem system_inj {G₁ G₂ : Greedoid α} :
    G₁.system = G₂.system ↔ G₁ = G₂ :=
  system_injective.eq_iff

/-- A coercion from `GreedoidLanguage` to `Greedoid`.
    Noncomputable as `GreedoidLanguage` is defined with `Set`. -/
@[coe]
noncomputable def ofGreedoidLanguage :
    GreedoidLanguage α → Greedoid α := fun L =>
  ⟨L, L.fromLanguageToSystem, relatedLanguageSystem_of_fromLanguageToSystem⟩

/-- A coercion from `GreedoidSystem` to `Greedoid`. -/
@[coe]
def ofGreedoidSystem : GreedoidSystem α → Greedoid α :=
  fun S => ⟨S.fromSystemToLanguage, S, relatedLanguageSystem_of_fromSystemToLanguage⟩

@[simp]
theorem ofGreedoidLanguage_eq : ofGreedoidLanguage G.language = G := by rw [← language_inj]; rfl

@[simp]
theorem ofGreedoidSystem_eq : ofGreedoidSystem G.system = G := by rw [← system_inj]; rfl

/-- `Greedoid` is decidable as `GreedoidSystem` is decidable. -/
instance : DecidableEq (Greedoid α) := fun G₁ G₂ =>
  if h : G₁.system = G₂.system
  then isTrue (eq_of_veq ((relatedLanguageSystem_eq G₁.related G₂.related).mpr h) h)
  else isFalse (fun h' => h (h' ▸ rfl))

instance : Fintype (Greedoid α) where
  elems := (@Finset.univ (GreedoidSystem α) _).map
    ⟨fun S => ofGreedoidSystem S, fun _ _ hS => system_inj.mpr hS⟩
  complete G := by
    simp only [Finset.mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and]
    exists G.system; simp only [ofGreedoidSystem_eq]

section Membership

theorem system_feasible_set_mem_mem {s : Finset α} : s ∈ G.system.feasibleSet ↔ s ∈ G := by rfl

theorem system_feasible_set_mem_memₛ {s : Finset α} : s ∈ G.system.feasibleSet ↔ s ∈ₛ G := by rfl

theorem language_language_mem_memₗ {l : List α} : l ∈ G.language.language ↔ l ∈ₗ G := by rfl

theorem emptyset_finsetMem : ∅ ∈ₛ G := G.system.containsEmpty

theorem nil_listMem : ([] : List α) ∈ₗ G := G.language.containsEmpty

theorem emptyset_mem : (∅ : Finset α) ∈ G := G.system.containsEmpty

theorem nil_toFinset_mem : [].toFinset ∈ G := G.system.containsEmpty

theorem listMem_nodup {l : List α} (hl : l ∈ₗ G) : l.Nodup := G.language.nodup hl

@[simp]
theorem finsetMem_mem_iff {s : Finset α} :
    s ∈ G ↔ s ∈ₛ G := by rfl

theorem listMem_language_toFinset_mem {l : List α} (hl : l ∈ₗ G) :
    l.toFinset ∈ₛ G :=
  toFinset_mem_greedoidSystem_of_mem_greedoidLanguage G.related hl

theorem finset_feasible_exists_list {s : Finset α} (hs : s ∈ₛ G) :
    ∃ l : List α, l ∈ₗ G ∧ l.toFinset = s := by
  simp only [Greedoid.listMem, exists_list_mem_greedoidLanguage_of_mem_greedoidSystem G.related hs]

theorem finsetMem_exchangeAxiom
  {s₁ : Finset α} (hs₁ : s₁ ∈ₛ G) {s₂ : Finset α} (hs₂ : s₂ ∈ₛ G) (hs : s₁.card > s₂.card) :
    ∃ x ∈ s₁ \ s₂, s₂ ∪ {x} ∈ₛ G := G.system.exchangeAxiom hs₁ hs₂ hs

theorem finsetMem_weakExchangeAxiom
  {s₁ : Finset α} (hs₁ : s₁ ∈ₛ G) {s₂ : Finset α} (hs₂ : s₂ ∈ₛ G) (hs : s₁.card = s₂.card + 1) :
    ∃ x ∈ s₁ \ s₂, s₂ ∪ {x} ∈ₛ G :=
  finsetMem_exchangeAxiom hs₁ hs₂ (by simp only [hs, lt_add_iff_pos_right])

end Membership

instance : Accessible G.system.feasibleSet :=
  ⟨G.system.containsEmpty, G.system.accessible⟩

theorem exchangeAxiom : _root_.exchangeAxiom G.system.feasibleSet :=
  G.system.exchangeAxiom

theorem weakExchangeAxiom : _root_.weakExchangeAxiom G.system.feasibleSet :=
  exchangeAxiom_to_weakExchangeAxiom G.system.exchangeAxiom

-- TODO: Add theorem weakerExchangeAxiom.

instance : Language.Hereditary G.language.language :=
  ⟨G.language.containsEmpty, G.language.containsPrefix⟩

-- Possible typo at IV. Lemma 1.5
/-- Normal greedoid contains no loops. -/
class Normal (G : Greedoid α) where
  /-- Loops are elements of the ground set which is not contained in any feasible set. -/
  noLoops : {a : α} → ∃ X, X ∈ₛ G ∧ a ∈ X

/-- `Greedoid` is full if the ground set is feasible. -/
class Full (G : Greedoid α) where
  /-- Full greedoids contain its ground. -/
  full : Finset.univ ∈ₛ G

/-- The interval property is satisfied by matroids, antimatroids, and some greedoids. -/
class IntervalProperty (G : Greedoid α) where
  /-- If there are three intervals A ⊆ B ⊆ C and
      some x which A ∪ {x} and C ∪ {x} are both intervals,
      then B ∪ {x} is also an interval. -/
  intervalProperty : {A : Finset α} → A ∈ₛ G →
                     {B : Finset α} → B ∈ₛ G →
                     {C : Finset α} → C ∈ₛ G →
                     A ⊆ B → B ⊆ C → {x : α} → x ∉ C →
                     A ∪ {x} ∈ₛ G → C ∪ {x} ∈ₛ G → B ∪ {x} ∈ₛ G

/-- Matroid is an interval greedoid without lower bound. -/
class IntervalPropertyWithoutLowerBound (G : Greedoid α) where
  /-- If there are two intervals A ⊆ B and
      some x ∉ B which B ∪ {x} is an interval,
      then A ∪ {x} is also an interval. -/
  intervalPropertyWOLowerBound : {A : Finset α} → A ∈ₛ G →
                                 {B : Finset α} → B ∈ₛ G → A ⊆ B →
                                 {x : α} → x ∉ B →
                                 B ∪ {x} ∈ₛ G → A ∪ {x} ∈ₛ G

instance [IntervalPropertyWithoutLowerBound G] : IntervalProperty G where
  intervalProperty := by
    intro _ _ _ hB _ hC _ h₂ _ hx _ hCx
    exact IntervalPropertyWithoutLowerBound.intervalPropertyWOLowerBound hB hC h₂ hx hCx

/-- Antimatroid is an interval greedoid without upper bound. -/
class IntervalPropertyWithoutUpperBound (G : Greedoid α) where
  /-- If there are two intervals B ⊆ A and
      some x ∉ A which B ∪ {x} is an interval,
      then A ∪ {x} is also an interval. -/
  intervalPropertyWOUpperBound : {A : Finset α} → A ∈ₛ G →
                                 {B : Finset α} → B ∈ₛ G → B ⊆ A →
                                 {x : α} → x ∉ A →
                                 B ∪ {x} ∈ₛ G → A ∪ {x} ∈ₛ G

instance [IntervalPropertyWithoutUpperBound G] : IntervalProperty G where
  intervalProperty := by
    intro _ hA _ hB _ _ h₁ h₂ _ hx hAx _
    exact IntervalPropertyWithoutUpperBound.intervalPropertyWOUpperBound
      hB hA h₁ (fun h => hx (h₂ h)) hAx

-- TODO: instance [IntervalPropertyWithoutUpperBound G] : Full G where full := by sorry

/-- A base of a greedoid. -/
def base (G : Greedoid α) := _root_.base G.system.feasibleSet

/-- A bases of a given set `s` of a greedoid. -/
def bases (G : Greedoid α) (s : Finset α) := _root_.bases G.system.feasibleSet s

theorem base_bases_eq : G.base = G.bases (@Finset.univ α _) := _root_.base_bases_eq

theorem basis_feasible {s b : Finset α} (hb : b ∈ G.bases s) : b ∈ G.system.feasibleSet := by
  simp_all [bases, _root_.bases]

theorem basis_def {s b : Finset α} :
    b ∈ G.bases s ↔ (b ∈ₛ G ∧ b ⊆ s ∧ (∀ a ∈ s, a ∉ b → b ∪ {a} ∉ₛ G)) := by
  constructor <;> intro h
  . simp [bases, _root_.bases] at h
    apply And.intro h.1 (And.intro h.2.1 _)
    tauto
  . simp [bases, _root_.bases]
    apply And.intro h.1 (And.intro h.2.1 _)
    intro a ha₁ ha₂
    simp only at h
    by_contra' h'
    exact h.2.2 _ ha₁ h' ha₂

theorem bases_nonempty {s : Finset α} : Nonempty (G.bases s) :=
  accessible_bases_nonempty

theorem bases_card_eq {s : Finset α}
  {b₁ : Finset α} (hb₁ : b₁ ∈ G.bases s)
  {b₂ : Finset α} (hb₂ : b₂ ∈ G.bases s) :
    b₁.card = b₂.card :=
  exchangeAxiom_bases_card_iff.mp G.exchangeAxiom hb₁ hb₂

theorem basis_of_full_unique [Full G] : ∃! b, b ∈ G.base := by
  exists univ
  simp only; constructor
  . simp [base, _root_.base]
    exact Full.full
  . intro s hs
    apply eq_univ_of_card
    apply @bases_card_eq _ _ _ G univ <;> rw [← base_bases_eq]
    . exact hs
    . simp [base, _root_.base]
      exact Full.full

theorem bases_of_full_card [Full G] : G.base.card = 1 := by
  let ⟨_, _⟩ := (Finset.singleton_iff_unique_mem (G.base)).mpr basis_of_full_unique
  simp_all

/-- A cardinality of largest feasible subset of `s` in `G`. -/
def rank (G : Greedoid α) (s : Finset α) :=
  ((G.system.feasibleSet.filter (fun s' => s' ⊆ s)).image (fun t => t.card)).max.unbot (by
    intro h
    simp [Finset.max_eq_bot, filter_eq_empty_iff] at h
    exact h _ G.system.containsEmpty (by simp only [empty_subset]))

section rank

variable {s t : Finset α} {x y : α}

theorem rank_eq_bases_card :
    ∀ b ∈ G.bases s, b.card = G.rank s := by
  by_contra'
  let ⟨b, hb₁, hb₂⟩ := this; clear this
  rw [← lt_or_lt_iff_ne] at hb₂
  apply hb₂.elim <;> intro h <;> clear hb₂ <;> clear hb₂
  . sorry
  . sorry

@[simp]
theorem rank_empty : G.rank ∅ = 0 := by
  simp [rank, Finset.subset_empty, Finset.filter_eq', G.system.containsEmpty]

theorem rank_le_card : G.rank s ≤ s.card := sorry

theorem subset_then_rank_le (hs : s ⊆ t) : G.rank s ≤ G.rank t := sorry

theorem local_submodularity
  (h₁ : G.rank s = G.rank (s ∪ {x}))
  (h₂ : G.rank s = G.rank (s ∪ {y})) :
    G.rank (s ∪ {x, y}) = G.rank s := sorry

theorem stronger_local_submodularity_left
  (h₁ : G.rank s = G.rank (s ∩ t))
  (h₂ : G.rank t = G.rank (s ∩ t)) :
    G.rank s = G.rank (s ∪ t) := sorry

theorem stronger_local_submodularity_right
  (h₁ : G.rank s = G.rank (s ∩ t))
  (h₂ : G.rank t = G.rank (s ∩ t)) :
    G.rank t = G.rank (s ∪ t) := by
  simp [h₂, ← h₁, stronger_local_submodularity_left h₁ h₂]

-- TODO: Looking for better name
theorem rank_lt_succ_lt
  (hs₁ : G.rank s < G.rank (s ∪ {x}))
  (hs₂ : G.rank s < G.rank (s ∪ {y})) :
    G.rank s + 1 < G.rank (s ∪ {x, y}) := sorry

theorem rank_of_feasible (hs : s ∈ₛ G) : G.rank s = s.card := sorry

theorem rank_of_infeasible (hs : s ∉ₛ G) : G.rank s < s.card := sorry

@[simp]
theorem rank_eq_card_iff_feasible : G.rank s = s.card ↔ s ∈ₛ G := by
  apply Iff.intro _ (fun h => rank_of_feasible h)
  intro h
  have := mt (@rank_of_infeasible _ _ _ G s)
  simp at this
  apply this
  simp only [h, le_refl]

theorem ssubset_of_feasible_rank (hs : s ∈ₛ G) (h : t ⊂ s) : G.rank t < G.rank s := sorry

/-- List of axioms for rank of greedoid. -/
def greedoidRankAxioms (r : Finset α → ℕ) :=
  (r ∅ = 0) ∧ (∀ s, r s ≤ s.card) ∧ (∀ s t, s ⊆ t → r s ≤ r t) ∧
  (∀ s x y, r s = r (s ∪ {x}) → r s = r (s ∪ {y}) → r s = r (s ∪ {x, y}))

theorem greedoidRankAxioms_unique_greedoid {r : Finset α → ℕ} (hr : greedoidRankAxioms r) :
    ∃! G : Greedoid α, G.rank = r := sorry

/-- Rank function satisfying `greedoidRankAxioms` generates a unique greedoid. -/
protected def rank.toGreedoid (r : Finset α → ℕ) (hr : greedoidRankAxioms r) : Greedoid α :=
  Fintype.choose (fun G => G.rank = r) (greedoidRankAxioms_unique_greedoid hr)

end rank

/-- Closure of `s` is the largest set which contains `s` and have the same rank with `s`. -/
def closure (G : Greedoid α) (s : Finset α) : Finset α:=
  (@Finset.univ α _).filter (fun x => G.rank (s ∪ {x}) = G.rank s)

section closure

variable {s t : Finset α} {x y : α}

theorem self_subset_closure : s ⊆ G.closure s := by
  simp [closure]
  intro x hx
  have hx : {x} ⊆ s := by simp only [singleton_subset_iff, hx]
  simp [Finset.union_eq_left_iff_subset.mpr hx]

@[simp]
theorem rank_closure_eq_rank_self : G.rank (G.closure s) = G.rank s := sorry

theorem feasible_iff_elem_notin_closure_minus_elem :
    s ∈ₛ G ↔ ∀ x ∈ s, x ∉ G.closure (s \ {x}) := by
  simp [closure]
  constructor <;> intro h
  . intro x hx h'
    have hx : {x} ⊆ s := by simp only [singleton_subset_iff, hx]
    simp [Finset.union_eq_left_iff_subset.mpr hx] at h'
    rw [rank_of_feasible h] at h'
    have := @ssubset_of_feasible_rank _ _ _ G s (s \ {x}) h sorry
    simp [← h', rank_eq_card_iff_feasible.mpr h] at this
  . sorry

theorem closure_eq_of_subset_adj_closure (hst : s ⊆ G.closure t) (hts : t ⊆ G.closure s) :
    G.closure s = G.closure t := sorry

theorem closure_idempotent : G.closure (G.closure s) = G.closure s :=
  closure_eq_of_subset_adj_closure (by simp)
    (Finset.Subset.trans self_subset_closure self_subset_closure)

theorem closure_exchange_property
  (hx : x ∉ s) (hy : y ∉ s) (hs : s ∪ {x} ∈ₛ G)
  (h : x ∈ G.closure (s ∪ {y})) :
    y ∈ G.closure (s ∪ {x}) := sorry

/-- `cospanning` is an equivalence relation in `2^E`. -/
def cospanning (G : Greedoid α) (s t : Finset α) := G.closure s = G.closure t

section cospanning

theorem cospanning_refl : ∀ s, G.cospanning s s := by simp [cospanning]

theorem cospanning_symm (h : G.cospanning s t) : G.cospanning t s := by
  simp only [cospanning] at h; simp only [cospanning, h]

theorem cospanning_comm : G.cospanning s t ↔ G.cospanning t s :=
  ⟨cospanning_symm, cospanning_symm⟩

theorem cospanning_trans {s t u : Finset α}
  (hst : G.cospanning s t) (htu : G.cospanning t u) :
    G.cospanning s u := by
  simp only [cospanning] at hst htu; simp only [cospanning, hst, htu]

theorem cospanning_eqv : Equivalence (G.cospanning) :=
  ⟨cospanning_refl, cospanning_symm, cospanning_trans⟩

theorem cospanning_rel_left_union (h : G.cospanning s t) : G.cospanning s (s ∪ t) := sorry

theorem cospanning_rel_right_union (h : G.cospanning s t) : G.cospanning (s ∪ t) t :=
  cospanning_trans (cospanning_symm (cospanning_rel_left_union h)) h

theorem cospanning_rel_between_subset_left {s t u : Finset α}
  (hst : s ⊆ t) (htu : t ⊆ u) (hsu : G.cospanning s u) :
    G.cospanning s t := sorry

theorem cospanning_rel_between_subset_right {s t u : Finset α}
  (hst : s ⊆ t) (htu : t ⊆ u) (hsu : G.cospanning s u) :
    G.cospanning t u :=
  G.cospanning_trans (cospanning_symm (cospanning_rel_between_subset_left hst htu hsu)) hsu

theorem cospanning_rel_ex
  (h₁ : G.cospanning (s ∪ {y}) (s ∪ {x, y}))
  (h₂ : ¬ G.cospanning (s ∪ {x}) (s ∪ {x, y})) :
    ∃ z ∈ s ∪ {x}, G.cospanning ((s ∪ {x}) \ {z}) (s ∪ {x}) := sorry

theorem cospanning_rel_ex'
  (h₁ : G.cospanning (s ∪ {y}) (s ∪ {x, y}))
  (h₂ : ¬ G.cospanning (s ∪ {x}) (s ∪ {x, y})) :
    ∃ z ∈ s ∪ {x}, G.cospanning (s ∪ {x}) ((s ∪ {x}) \ {z}) :=
  let ⟨z, hz⟩ := cospanning_rel_ex h₁ h₂
  ⟨z, hz.1, G.cospanning_symm hz.2⟩

end cospanning

end closure

end Greedoid
