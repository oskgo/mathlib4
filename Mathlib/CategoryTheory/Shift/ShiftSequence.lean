import Mathlib.CategoryTheory.Shift.HasCommShift
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

open CategoryTheory Category ZeroObject Limits

variable {C D A : Type _} [Category C] [Category D] [Category A]
  (F : C ⥤ A) {π : C ⥤ D} {H : D ⥤ A} (e : π ⋙ H ≅ F)
  (M G : Type _) [AddMonoid M] [AddGroup G] [HasShift C M] [HasShift C G]
  [HasShift D M]

namespace CategoryTheory

namespace Functor

-- the idea of `ShiftSequence` is to attach to the functor `H^0`
-- (on cochain complexes, the homotopy category, or the derived category)
-- the whole sequence of functor `H^n` for all `n : ℤ`, so that the
-- homology sequence associated to a distinguished triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧`
-- will be like `H^n X ⟶ H^n Y ⟶ H^n Z ⟶ H^(n+1) X` rather than
-- `H^0 (X⟦n⟧) ⟶ H^0 (Y⟦n⟧]) ⟶ H^0 (Z⟦n⟧]) ⟶ H^0 (X⟦n+1⟧]))`.
--
-- similarly, when `RF : C ⥤ DerivedCategory A` is a
-- triangulated functor, `RF ⋙ H^0` shall come together
-- with the sequence of $R^n F$ which are the `RF ⋙ H^n`,
-- see `ShiftSequence.leftComp`.
--

class ShiftSequence where
  sequence : M → C ⥤ A
  isoZero : sequence 0 ≅ F
  shiftIso (n a a' : M) (ha' : n + a = a') : shiftFunctor C n ⋙ sequence a ≅ sequence a'
  shiftIso_zero (a : M) : shiftIso 0 a a (zero_add a) =
    isoWhiskerRight (shiftFunctorZero C M) _ ≪≫ leftUnitor _
  shiftIso_add : ∀ (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a''),
    shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) =
      isoWhiskerRight (shiftFunctorAdd C m n) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (shiftIso n a a' ha') ≪≫ shiftIso m a' a'' ha''

noncomputable def ShiftSequence.tautological : ShiftSequence F M where
  sequence n := shiftFunctor C n ⋙ F
  isoZero := isoWhiskerRight (shiftFunctorZero C M) F ≪≫ F.rightUnitor
  shiftIso n a a' ha' := (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (shiftFunctorAdd' C n a a' ha').symm _
  shiftIso_zero a := by
    dsimp
    rw [shiftFunctorAdd'_zero_add]
    aesop_cat
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext X
    dsimp
    simp only [id_comp, ← Functor.map_comp]
    congr
    simpa only [← cancel_epi ((shiftFunctor C a).map ((shiftFunctorAdd C m n).hom.app X)),
      shiftFunctorAdd'_eq_shiftFunctorAdd, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      Functor.map_id, id_comp] using shiftFunctorAdd'_assoc_inv_app m n a (m+n) a' a'' rfl ha'
        (by rw [← ha'', ← ha', add_assoc]) X

section

variable {M}
variable [F.ShiftSequence M]

def shift (n : M) : C ⥤ A := ShiftSequence.sequence F n

def shiftIso (n a a' : M) (ha' : n + a = a') : shiftFunctor C n ⋙ F.shift a ≅ F.shift a' :=
  ShiftSequence.shiftIso n a a' ha'

@[reassoc (attr := simp 1100)]
lemma shiftIso_hom_naturality {X Y : C} (n a a' : M) (ha' : n + a = a') (f : X ⟶ Y) :
    (shift F a).map (f⟦n⟧') ≫ (shiftIso F n a a' ha').hom.app Y =
      (shiftIso F n a a' ha').hom.app X ≫ (shift F a').map f :=
  (F.shiftIso n a a' ha').hom.naturality f

@[reassoc (attr := simp 1100)]
lemma shiftIso_inv_naturality {X Y : C} (n a a' : M) (ha' : n + a = a') (f : X ⟶ Y) :
    (shift F a').map f ≫ (shiftIso F n a a' ha').inv.app Y =
      (shiftIso F n a a' ha').inv.app X ≫ (shift F a).map (f⟦n⟧') :=
  (F.shiftIso n a a' ha').inv.naturality f

variable (M)

def isoShiftZero : F.shift (0 : M) ≅ F := ShiftSequence.isoZero

variable {M}

def isoShift (n : M) : shiftFunctor C n ⋙ F ≅ F.shift n :=
  isoWhiskerLeft _ (F.isoShiftZero M).symm ≪≫ F.shiftIso _ _ _ (add_zero n)

@[reassoc]
lemma isoShift_hom_naturality (n : M) {X Y : C} (f : X ⟶ Y) :
  F.map (f⟦n⟧') ≫ (F.isoShift n).hom.app Y =
    (F.isoShift n).hom.app X ≫ (F.shift n).map f :=
  (F.isoShift n).hom.naturality f

attribute [simp] isoShift_hom_naturality

@[reassoc]
lemma isoShift_inv_naturality (n : M) {X Y : C} (f : X ⟶ Y) :
  (F.shift n).map f ≫ (F.isoShift n).inv.app Y =
    (F.isoShift n).inv.app X ≫ F.map (f⟦n⟧') :=
  (F.isoShift n).inv.naturality f

lemma shiftIso_zero (a : M) : F.shiftIso 0 a a (zero_add a) =
    isoWhiskerRight (shiftFunctorZero C M) _ ≪≫ leftUnitor _ :=  ShiftSequence.shiftIso_zero a

@[simp]
lemma shiftIso_zero_hom_app (a : M) (X : C) :
    (F.shiftIso 0 a a (zero_add a)).hom.app X =
      (shift F a).map ((shiftFunctorZero C M).hom.app X) := by
  simp [F.shiftIso_zero a]

@[simp]
lemma shiftIso_zero_inv_app (a : M) (X : C) :
    (F.shiftIso 0 a a (zero_add a)).inv.app X =
      (shift F a).map ((shiftFunctorZero C M).inv.app X) := by
  simp [F.shiftIso_zero a]

lemma shiftIso_add (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') :
    F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) =
      isoWhiskerRight (shiftFunctorAdd C m n) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (F.shiftIso n a a' ha') ≪≫ F.shiftIso m a' a'' ha'' :=
  ShiftSequence.shiftIso_add _ _ _ _ _ _ _

lemma shiftIso_add_hom_app (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).hom.app X =
    (shift F a).map ((shiftFunctorAdd C m n).hom.app X) ≫
      (shiftIso F n a a' ha').hom.app ((shiftFunctor C m).obj X) ≫
      (shiftIso F m a' a'' ha'').hom.app X := by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

lemma shiftIso_add_inv_app (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).inv.app X =
      (shiftIso F m a' a'' ha'').inv.app X ≫
      (shiftIso F n a a' ha').inv.app ((shiftFunctor C m).obj X) ≫
    (shift F a).map ((shiftFunctorAdd C m n).inv.app X) := by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

lemma shiftIso_add' (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
  (ha' : n + a = a') (ha'' : m + a' = a'') :
    F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc]) =
      isoWhiskerRight (shiftFunctorAdd' C m n _ hnm) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (F.shiftIso n a a' ha') ≪≫ F.shiftIso m a' a'' ha'' := by
  subst hnm
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd, shiftIso_add]

lemma shiftIso_add'_hom_app (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
    (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).hom.app X =
    (shift F a).map ((shiftFunctorAdd' C m n mn hnm).hom.app X) ≫
      (shiftIso F n a a' ha').hom.app ((shiftFunctor C m).obj X) ≫
      (shiftIso F m a' a'' ha'').hom.app X := by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

lemma shiftIso_add'_inv_app (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
    (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).inv.app X =
      (shiftIso F m a' a'' ha'').inv.app X ≫
      (shiftIso F n a a' ha').inv.app ((shiftFunctor C m).obj X) ≫
    (shift F a).map ((shiftFunctorAdd' C m n mn hnm).inv.app X) := by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

def shiftMap {X Y : C} {n : M} (f : X ⟶ Y⟦n⟧) (a a' : M) (ha' : n + a = a') :
    (F.shift a).obj X ⟶ (F.shift a').obj Y :=
  (F.shift a).map f ≫ (F.shiftIso _ _ _ ha').hom.app Y

@[reassoc]
lemma shiftMap_comp {X Y Z : C} {n : M} (f : X ⟶ Y⟦n⟧) (g : Y ⟶ Z) (a a' : M) (ha' : n + a = a') :
    F.shiftMap (f ≫ g⟦n⟧') a a' ha' = F.shiftMap f a a' ha' ≫ (F.shift a').map g := by
  simp [shiftMap]

@[reassoc]
lemma shiftMap_comp' {X Y Z : C} {n : M} (f : X ⟶ Y) (g : Y ⟶ Z⟦n⟧) (a a' : M) (ha' : n + a = a') :
    F.shiftMap (f ≫ g) a a' ha' = (F.shift a).map f ≫ F.shiftMap g a a' ha' := by
  simp [shiftMap]

lemma shiftIso_hom_app_comp_shiftMap {X Y : C} {m : M} (f : X ⟶ Y⟦m⟧) (n mn : M) (hnm : m + n = mn)
    (a a' a'' : M)
    (ha' : n + a = a') (ha'' : m + a' = a'') :
    (F.shiftIso n a a' ha').hom.app X ≫ F.shiftMap f a' a'' ha'' =
      (F.shift a).map (f⟦n⟧') ≫ (F.shift a).map ((shiftFunctorAdd' C m n mn hnm).inv.app Y) ≫
        (F.shiftIso mn a a'' (by rw [← ha'', ← ha', ← hnm, add_assoc])).hom.app Y := by
  simp only [F.shiftIso_add'_hom_app n m mn hnm a a' a'' ha' ha'' Y,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    id_comp, comp_obj, shiftIso_hom_naturality_assoc, shiftMap]

variable {G}
variable [F.ShiftSequence G]

lemma shiftIso_hom_app_comp_shiftMap_of_add_eq_zero {X Y : C} {m : G} (f : X ⟶ Y⟦m⟧)
    (n : G) (hnm : n + m = 0) (a a' : G) (ha' : m + a = a') :
    (F.shiftIso n a' a (by rw [← ha', ← add_assoc, hnm, zero_add])).hom.app X ≫
      F.shiftMap f a a' ha' =
    (F.shift a').map (f⟦n⟧' ≫ (shiftFunctorCompIsoId C m n
      (by rw [← add_left_inj m, add_assoc, hnm, zero_add, add_zero])).hom.app Y) := by
  have hnm' : m + n = 0 := by
    rw [← add_left_inj m, add_assoc, hnm, zero_add, add_zero]
  simp only [F.shiftIso_hom_app_comp_shiftMap f n 0 hnm' a' a,
    shiftIso_zero_hom_app, shiftFunctorCompIsoId,
    Iso.trans_hom, Iso.symm_hom, ← Functor.map_comp,
    NatTrans.comp_app]

section

variable [HasZeroMorphisms C] [HasZeroMorphisms A] [F.PreservesZeroMorphisms]
  [∀ (n : M), (shiftFunctor C n).PreservesZeroMorphisms]

instance (n : M) :
    (F.shift n).PreservesZeroMorphisms :=
  preservesZeroMorphisms_of_iso (F.isoShift n)

@[simp]
lemma shiftMap_zero
    (X Y : C) (n a a' : M) (ha' : n + a = a') :
  F.shiftMap (0 : X ⟶ Y⟦n⟧) a a' ha' = 0 := by
    simp [shiftMap]

end

section

variable [Preadditive C] [Preadditive A] [F.Additive]
  [∀ (n : M), (shiftFunctor C n).Additive]

instance (n : M) : (F.shift n).Additive :=
  additive_of_iso (F.isoShift n)

end

end

namespace ShiftSequence

variable {M}

@[simp]
lemma tautological_sequence (n : M) :
    @Functor.shift _ _ _ _ _ _ _ _ (tautological F M) n = shiftFunctor C n ⋙ F := rfl

variable (M) {F}

def leftComp [π.HasCommShift M] [H.ShiftSequence M] : F.ShiftSequence M where
  sequence n := π ⋙ H.shift n
  isoZero := isoWhiskerLeft π (H.isoShiftZero M) ≪≫ e
  shiftIso n a a' ha' := (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (π.commShiftIso n) _ ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft π (H.shiftIso n a a' ha')
  shiftIso_zero a := by
    ext K
    dsimp
    simp only [shiftIso_zero_hom_app, id_obj, id_comp, comp_id, ← Functor.map_comp,
      commShiftIso_zero, HasCommShift.iso_zero_hom_app, assoc, Iso.inv_hom_id_app]
  shiftIso_add n m a a' a'' ha' ha'':= by
    ext K
    dsimp
    simp only [H.shiftIso_add_hom_app n m a a' a'' ha' ha'', assoc,
      commShiftIso_add, HasCommShift.iso_add_hom_app, ← Functor.map_comp_assoc,
      id_comp, Iso.inv_hom_id_app, comp_obj, comp_id]
    simp only [map_comp, assoc, shiftIso_hom_naturality_assoc]

instance [π.HasCommShift M] [H.ShiftSequence M] : (π ⋙ H).ShiftSequence M :=
  leftComp (Iso.refl _) _

end ShiftSequence


end Functor

end CategoryTheory
