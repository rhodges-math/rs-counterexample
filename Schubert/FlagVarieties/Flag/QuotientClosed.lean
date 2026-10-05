import Schubert.FlagVarieties.Flag.Quotient
import Schubert.FlagVarieties.LineBundle.Restriction

/-!
# `X = π⁻¹(X) / B` for closed subschemes `X ⊆ Flₙ`

For every closed subscheme `X ⊆ Flₙ` (over every commutative ring), the projection
`P_X = π⁻¹(X) ⟶ X` is the coequalizer of the projection and the right action
`P_X ×_R B ⇉ P_X` in schemes (`FlagVarieties.isColimitPreimageProj`): it has sections over the
cells `X ∩ bigCell v`, and its fibres are `B`-orbits (`FlagVarieties.preimage_comp_eq_of_proj_eq`).
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {R : Type u} [CommRing R] {n : ℕ} {I : (FlagScheme R n).IdealSheafData}

/-- **`B`-invariant morphisms out of `P_X` are constant on the fibres of `P_X ⟶ X`.** -/
theorem preimage_comp_eq_of_proj_eq {W Y : Scheme.{u}} (h : preimageScheme R n I ⟶ Y)
    (hh : preimageAct R n I ≫ h = pullback.fst _ _ ≫ h) (a a' : W ⟶ preimageScheme R n I)
    (ha : a ≫ preimageProj R n I = a' ≫ preimageProj R n I) : a ≫ h = a' ≫ h := by
  refine Scheme.hom_ext_of_forall _ _ fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine ⟨U, hxU, ?_⟩
  have : IsAffine U := hU
  let b := Scheme.Opens.ι U ≫ a
  let b' := Scheme.Opens.ι U ≫ a'
  have hq : b ≫ preimageProj R n I = b' ≫ preimageProj R n I := by
    simp only [b, b', Category.assoc, ha]
  have hπ : (b ≫ preimageι R n I) ≫ FlagScheme.orbitMap R n =
      (b' ≫ preimageι R n I) ≫ FlagScheme.orbitMap R n := by
    have h2 := congrArg (· ≫ I.subschemeι) hq
    simp only [Category.assoc] at h2 ⊢
    rw [pullback.condition]
    exact h2
  obtain ⟨β, hβ, e⟩ := exists_mulRight_eq (b ≫ preimageι R n I) (b' ≫ preimageι R n I) hπ
  have hβ' : b ≫ preimageToSpec R n I = β ≫ BorelScheme.toSpec R n := by
    rw [← hβ]
    simp only [preimageToSpec, Category.assoc]
  let m : (U : Scheme.{u}) ⟶ PreimageProd R n I := pullback.lift b β hβ'
  have hm1 : m ≫ preimageProdMap R n I = pullback.lift (b ≫ preimageι R n I) β hβ := by
    apply pullback.hom_ext
    · rw [Category.assoc, preimageProdMap, pullback.lift_fst, pullback.lift_fst_assoc,
        pullback.lift_fst]
    · rw [Category.assoc, preimageProdMap, pullback.lift_snd, pullback.lift_snd_assoc,
        pullback.lift_snd, Category.comp_id]
  have hm : m ≫ preimageAct R n I = b' := by
    apply pullback.hom_ext
    · rw [Category.assoc, preimageAct, pullback.lift_fst, ← Category.assoc, hm1, e]
    · rw [Category.assoc, preimageAct, pullback.lift_snd, pullback.lift_fst_assoc, hq]
  change b ≫ h = b' ≫ h
  rw [← hm, Category.assoc m, hh, pullback.lift_fst_assoc]

variable (R n I)

theorem isOpenCover_bigCellX : TopologicalSpace.IsOpenCover (bigCellX R n I) := by
  rw [TopologicalSpace.IsOpenCover, eq_top_iff]
  intro x _
  obtain ⟨v, hv⟩ := exists_mem_bigCell R (I.subschemeι x)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨v, hv⟩

/-- The cells `X ∩ bigCell v`, as an open cover of `X`. -/
abbrev bigCellXCover : I.subscheme.OpenCover where
  I₀ := Equiv.Perm (Fin n)
  X v := bigCellX R n I v
  f v := (bigCellX R n I v).ι
  mem₀ := (I.subscheme.openCoverOfIsOpenCover (bigCellX R n I) (isOpenCover_bigCellX R n I)).mem₀

@[reassoc (attr := simp)] theorem preimageLocalDataE_proj (v : Equiv.Perm (Fin n)) :
    preimageLocalDataE R n I v ≫ preimageProj R n I = (bigCellX R n I v).ι :=
  pullback.lift_snd _ _ _

variable {R n I}

/-- The morphism `X ⟶ Y` induced by a `B`-invariant morphism `P_X ⟶ Y`. -/
def preimageDesc {Y : Scheme.{u}} (h : preimageScheme R n I ⟶ Y)
    (hh : preimageAct R n I ≫ h = pullback.fst _ _ ≫ h) : I.subscheme ⟶ Y :=
  (bigCellXCover R n I).glueMorphisms (fun v => preimageLocalDataE R n I v ≫ h) (fun x y => by
    rw [← Category.assoc, ← Category.assoc]
    apply preimage_comp_eq_of_proj_eq h hh
    rw [Category.assoc, Category.assoc, preimageLocalDataE_proj, preimageLocalDataE_proj]
    exact pullback.condition)

theorem bigCellX_ι_preimageDesc {Y : Scheme.{u}} (h : preimageScheme R n I ⟶ Y)
    (hh : preimageAct R n I ≫ h = pullback.fst _ _ ≫ h) (v : Equiv.Perm (Fin n)) :
    (bigCellX R n I v).ι ≫ preimageDesc h hh = preimageLocalDataE R n I v ≫ h :=
  Scheme.Cover.ι_glueMorphisms (bigCellXCover R n I) _ _ v

@[reassoc] theorem preimageProj_preimageDesc {Y : Scheme.{u}} (h : preimageScheme R n I ⟶ Y)
    (hh : preimageAct R n I ≫ h = pullback.fst _ _ ≫ h) :
    preimageProj R n I ≫ preimageDesc h hh = h := by
  refine Scheme.hom_ext_of_forall _ _ fun x => ?_
  obtain ⟨v, hv⟩ := exists_mem_bigCell R (I.subschemeι (preimageProj R n I x))
  refine ⟨preimageProj R n I ⁻¹ᵁ bigCellX R n I v, hv, ?_⟩
  rw [← morphismRestrict_ι_assoc, bigCellX_ι_preimageDesc, ← Category.assoc]
  apply preimage_comp_eq_of_proj_eq h hh
  rw [Category.assoc, preimageLocalDataE_proj, morphismRestrict_ι]

theorem preimageDesc_ext {Y : Scheme.{u}} {f g : I.subscheme ⟶ Y}
    (h : preimageProj R n I ≫ f = preimageProj R n I ≫ g) : f = g := by
  refine (bigCellXCover R n I).hom_ext _ _ fun v => ?_
  change (bigCellX R n I v).ι ≫ f = (bigCellX R n I v).ι ≫ g
  rw [← preimageLocalDataE_proj_assoc, h, preimageLocalDataE_proj_assoc]

variable (R n I)

/-- **`X = P_X / B`**: for every closed subscheme `X ⊆ Flₙ`, the projection `P_X = π⁻¹(X) ⟶ X` is
the coequalizer of the projection and the right action `P_X ×_R B ⇉ P_X`, in schemes. -/
def isColimitPreimageProj :
    IsColimit (Cofork.ofπ (preimageProj R n I) (preimageAction R n I).act_q) :=
  Cofork.IsColimit.mk' _ fun s => ⟨preimageDesc s.π s.condition,
    preimageProj_preimageDesc _ _, fun {m} hm => preimageDesc_ext
      ((hm : preimageProj R n I ≫ m = s.π).trans (preimageProj_preimageDesc _ _).symm)⟩

end FlagVarieties
