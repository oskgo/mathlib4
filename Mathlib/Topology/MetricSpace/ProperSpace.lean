import Mathlib.Topology.MetricSpace.Basic

open TopologicalSpace Metric Set Filter Bornology
open scoped ENNReal

section PseudoMetricSpace

variable {X : Type*} [PseudoMetricSpace X]

/-- A pseudometric space is proper if all closed balls are compact. -/
class ProperSpace (α : Type*) [PseudoMetricSpace α] : Prop where
  /-- In a proper (pseudo)metric space, all closed balls are compact. -/
  isCompact_closedBall : ∀ x : α, ∀ r, IsCompact (closedBall x r)
#align proper_space ProperSpace

export ProperSpace (isCompact_closedBall)

-- A compact pseudometric space is proper
-- see Note [lower instance priority]
instance (priority := 100) ProperSpace.of_compactSpace [CompactSpace X] : ProperSpace X :=
  ⟨fun _ _ => isClosed_ball.isCompact⟩
#align proper_of_compact ProperSpace.of_compactSpace

variable [ProperSpace X]

/-- In a proper pseudometric space, all spheres are compact. -/
theorem isCompact_sphere (x : X) (r : ℝ) : IsCompact (sphere x r) :=
  (isCompact_closedBall x r).of_isClosed_subset isClosed_sphere sphere_subset_closedBall
#align is_compact_sphere isCompact_sphere

/-- In a proper pseudometric space, any sphere is a `CompactSpace` when considered as a subtype. -/
instance Metric.sphere.compactSpace (x : X) (r : ℝ) : CompactSpace (sphere x r) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

/-- If all closed balls of large enough radius are compact, then the space is proper. Especially
useful when the lower bound for the radius is 0. -/
theorem properSpace_of_compact_closedBall_of_le (R : ℝ)
    (h : ∀ x : X, ∀ r, R ≤ r → IsCompact (closedBall x r)) : ProperSpace X :=
  ⟨fun x r => IsCompact.of_isClosed_subset (h x (max r R) (le_max_right _ _)) isClosed_ball
    (closedBall_subset_closedBall <| le_max_left _ _)⟩
#align proper_space_of_compact_closed_ball_of_le properSpace_of_compact_closedBall_of_le

-- see Note [lower instance priority]
/-- A proper space is locally compact -/
instance (priority := 100) LocallyCompactSpace.of_properSpace : LocallyCompactSpace X :=
  locallyCompactSpace_of_hasBasis (fun _ => nhds_basis_closedBall) fun _ _ _ =>
    isCompact_closedBall _ _
#align locally_compact_of_proper LocallyCompactSpace.of_properSpace

-- see Note [lower instance priority]
/-- A proper space is complete -/
instance (priority := 100) CompleteSpace.of_properSpace : CompleteSpace X :=
  ⟨fun {f} hf => by
    /- We want to show that the Cauchy filter `f` is converging. It suffices to find a closed
      ball (therefore compact by properness) where it is nontrivial. -/
    obtain ⟨t, t_fset, ht⟩ : ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, dist x y < 1 :=
      (Metric.cauchy_iff.1 hf).2 1 zero_lt_one
    rcases hf.1.nonempty_of_mem t_fset with ⟨x, xt⟩
    have : closedBall x 1 ∈ f := mem_of_superset t_fset fun y yt => (ht y yt x xt).le
    rcases (isCompact_iff_totallyBounded_isComplete.1 (isCompact_closedBall x 1)).2 f hf
        (le_principal_iff.2 this) with
      ⟨y, -, hy⟩
    exact ⟨y, hy⟩⟩
#align complete_of_proper CompleteSpace.of_properSpace

-- see Note [lower instance priority]
/-- A proper pseudo metric space is sigma compact, and therefore second countable. -/
instance (priority := 100) TopologicalSpace.SecondCountableTopology.of_properSpace :
    SecondCountableTopology X := by
  -- We already have `sigmaCompactSpace_of_locallyCompact_secondCountable`, so we don't
  -- add an instance for `SigmaCompactSpace`.
  suffices SigmaCompactSpace X by exact EMetric.secondCountable_of_sigmaCompact X
  rcases em (Nonempty X) with (⟨⟨x⟩⟩ | hn)
  · exact ⟨⟨fun n => closedBall x n, fun n => isCompact_closedBall _ _, iUnion_closedBall_nat _⟩⟩
  · exact ⟨⟨fun _ => ∅, fun _ => isCompact_empty, iUnion_eq_univ_iff.2 fun x => (hn ⟨x⟩).elim⟩⟩
#align second_countable_of_proper TopologicalSpace.SecondCountableTopology.of_properSpace

/-- A binary product of proper spaces is proper. -/
instance Prod.properSpace {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [ProperSpace X] [ProperSpace Y] : ProperSpace (X × Y) where
  isCompact_closedBall := fun (x, y) r ↦ by
    rw [← closedBall_prod_same x y]
    exact (isCompact_closedBall x r).prod (isCompact_closedBall y r)
#align prod_proper_space Prod.properSpace

/-- A finite product of proper spaces is proper. -/
instance Pi.properSpace {α : Type*} {π : α → Type*} [Fintype α] [∀ a, PseudoMetricSpace (π a)]
    [∀ a, ProperSpace (π a)] : ProperSpace (∀ a, π a) := by
  refine' properSpace_of_compact_closedBall_of_le 0 fun x r hr => _
  rw [closedBall_pi _ hr]
  exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
#align pi_proper_space Pi.properSpace

instance : ProperSpace (Additive X) := ‹ProperSpace X›
instance : ProperSpace (Multiplicative X) := ‹ProperSpace X›
instance : ProperSpace Xᵒᵈ := ‹ProperSpace X›

variable {x : X} {r : ℝ} {s : Set X}

/-- The **Heine–Borel theorem**: In a proper space, a closed bounded set is compact. -/
theorem Metric.isCompact_of_isClosed_isBounded (hc : IsClosed s) (hb : IsBounded s) :
    IsCompact s := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, -⟩)
  · exact isCompact_empty
  · rcases hb.subset_closedBall x with ⟨r, hr⟩
    exact (isCompact_closedBall x r).of_isClosed_subset hc hr
#align metric.is_compact_of_is_closed_bounded Metric.isCompact_of_isClosed_isBounded

/-- The **Heine–Borel theorem**: In a proper space, the closure of a bounded set is compact. -/
theorem _root_.Bornology.IsBounded.isCompact_closure (h : IsBounded s) :
    IsCompact (closure s) :=
  isCompact_of_isClosed_isBounded isClosed_closure h.closure
#align metric.bounded.is_compact_closure Bornology.IsBounded.isCompact_closure

theorem Metric.compactSpace_iff_isBounded_univ :
    CompactSpace X ↔ IsBounded (univ : Set X) :=
  ⟨@isBounded_of_compactSpace X _ _, fun hb => ⟨isCompact_of_isClosed_isBounded isClosed_univ hb⟩⟩
#align metric.compact_space_iff_bounded_univ Metric.compactSpace_iff_isBounded_univ

/-- If a nonempty ball in a proper space includes a closed set `s`, then there exists a nonempty
ball with the same center and a strictly smaller radius that includes `s`. -/
theorem exists_pos_lt_subset_ball (hr : 0 < r) (hs : IsClosed s) (h : s ⊆ ball x r) :
    ∃ r' ∈ Ioo 0 r, s ⊆ ball x r' := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · exact ⟨r / 2, ⟨half_pos hr, half_lt_self hr⟩, empty_subset _⟩
  have : IsCompact s :=
    (isCompact_closedBall x r).of_isClosed_subset hs (h.trans ball_subset_closedBall)
  obtain ⟨y, hys, hy⟩ : ∃ y ∈ s, s ⊆ closedBall x (dist y x) :=
    this.exists_forall_ge hne (continuous_id.dist continuous_const).continuousOn
  have hyr : dist y x < r := h hys
  rcases exists_between hyr with ⟨r', hyr', hrr'⟩
  exact ⟨r', ⟨dist_nonneg.trans_lt hyr', hrr'⟩, hy.trans <| closedBall_subset_ball hyr'⟩
#align exists_pos_lt_subset_ball exists_pos_lt_subset_ball

/-- If a ball in a proper space includes a closed set `s`, then there exists a ball with the same
center and a strictly smaller radius that includes `s`. -/
theorem exists_lt_subset_ball (hs : IsClosed s) (h : s ⊆ ball x r) : ∃ r' < r, s ⊆ ball x r' := by
  cases' le_or_lt r 0 with hr hr
  · rw [ball_eq_empty.2 hr, subset_empty_iff] at h
    subst s
    exact (exists_lt r).imp fun r' hr' => ⟨hr', empty_subset _⟩
  · exact (exists_pos_lt_subset_ball hr hs h).imp fun r' hr' => ⟨hr'.1.2, hr'.2⟩
#align exists_lt_subset_ball exists_lt_subset_ball

theorem Metric.ediam_univ_eq_top_iff_noncompact :
    EMetric.diam (univ : Set X) = ∞ ↔ NoncompactSpace X := by
  rw [← not_compactSpace_iff, compactSpace_iff_isBounded_univ, isBounded_iff_ediam_ne_top,
    Classical.not_not]
#align metric.ediam_univ_eq_top_iff_noncompact Metric.ediam_univ_eq_top_iff_noncompact

@[simp]
theorem Metric.ediam_univ_of_noncompact [NoncompactSpace X] :
    EMetric.diam (univ : Set X) = ∞ :=
  ediam_univ_eq_top_iff_noncompact.mpr ‹_›
#align metric.ediam_univ_of_noncompact Metric.ediam_univ_of_noncompact

@[simp]
theorem Metric.diam_univ_of_noncompact [NoncompactSpace X] : diam (univ : Set X) = 0 := by
  simp [diam]
#align metric.diam_univ_of_noncompact Metric.diam_univ_of_noncompact

theorem Metric.exists_isLocalMin_mem_ball {α : Type*} [TopologicalSpace α]
    [LinearOrder α] [OrderTopology α] {f : X → α} {a z : X} {r : ℝ}
    (hf : ContinuousOn f (closedBall a r)) (hz : z ∈ closedBall a r)
    (hf1 : ∀ z' ∈ sphere a r, f z < f z') : ∃ z ∈ ball a r, IsLocalMin f z := by
  simp_rw [← closedBall_diff_ball] at hf1
  exact (isCompact_closedBall a r).exists_isLocalMin_mem_open ball_subset_closedBall hf hz hf1
    isOpen_ball
#align metric.exists_local_min_mem_ball Metric.exists_isLocalMin_mem_ball

theorem Metric.cobounded_eq_cocompact : cobounded X = cocompact X := by
  nontriviality X; inhabit X
  exact cobounded_le_cocompact.antisymm <| (hasBasis_cobounded_compl_closedBall default).ge_iff.2
    fun _ _ ↦ (isCompact_closedBall _ _).compl_mem_cocompact
#align comap_dist_right_at_top_eq_cocompact Metric.cobounded_eq_cocompact

theorem tendsto_dist_right_cocompact_atTop (x : X) :
    Tendsto (dist · x) (cocompact X) atTop :=
  (tendsto_dist_right_cobounded_atTop x).mono_left cobounded_eq_cocompact.ge
#align tendsto_dist_right_cocompact_at_top tendsto_dist_right_cocompact_atTop

theorem tendsto_dist_left_cocompact_atTop (x : X) :
    Tendsto (dist x) (cocompact X) atTop :=
  (tendsto_dist_left_cobounded_atTop x).mono_left cobounded_eq_cocompact.ge
#align tendsto_dist_left_cocompact_at_top tendsto_dist_left_cocompact_atTop

theorem comap_dist_left_atTop_eq_cocompact (x : X) :
    comap (dist x) atTop = cocompact X := by simp [cobounded_eq_cocompact]
#align comap_dist_left_at_top_eq_cocompact comap_dist_left_atTop_eq_cocompact

theorem finite_isBounded_inter_isClosed {K s : Set X} [DiscreteTopology s]
    (hK : IsBounded K) (hs : IsClosed s) : Set.Finite (K ∩ s) := by
  refine Set.Finite.subset (IsCompact.finite ?_ ?_) (Set.inter_subset_inter_left s subset_closure)
  · exact hK.isCompact_closure.inter_right hs
  · exact DiscreteTopology.of_subset inferInstance (Set.inter_subset_right _ s)

end PseudoMetricSpace

/-- The **Heine–Borel theorem**:
In a proper Hausdorff space, a set is compact if and only if it is closed and bounded. -/
theorem Metric.isCompact_iff_isClosed_bounded {X : Type*} [MetricSpace X] [ProperSpace X]
    {s : Set X} : IsCompact s ↔ IsClosed s ∧ IsBounded s :=
  ⟨fun h => ⟨h.isClosed, h.isBounded⟩, fun h => isCompact_of_isClosed_isBounded h.1 h.2⟩
#align metric.is_compact_iff_is_closed_bounded Metric.isCompact_iff_isClosed_bounded
