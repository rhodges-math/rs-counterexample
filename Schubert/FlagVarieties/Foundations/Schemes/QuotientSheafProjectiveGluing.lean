import Schubert.FlagVarieties.Foundations.Schemes.QuotientSheafAffineFrameCover

/-!
# Global Proj morphisms from ordered quotient line sheaves

All local coefficients are the original ordered quotient sections in
local sheaf frames. Affine exactness gives coprimality, and
comparison of sheaf frames gives the common-unit overlap
relations. Scheme descent then gives a global morphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v w

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {N : X.Modules}
  [N.IsQuasicoherent] (q : orderedFreeSheaf X ⟶ N) [Epi q]

/-- Local quotient coefficients and derived transition units give gluing data. -/
def sheafOpenPairData {ι : Type v} {U : ι → X.Opens}
    (hAffine : ∀ i, IsAffineOpen (U i))
    (frames : ∀ i, N.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i))) :
    ProjectiveLine.OpenPairData U := by
  classical
  choose units h0 h1 using fun i j => sheafFrames_overlap_common_unit q (frames i) (frames j)
  exact {
    delta := fun i => framedQuotientCoefficient q (U i) (frames i) ⟨0⟩
    epsilon := fun i => framedQuotientCoefficient q (U i) (frames i) ⟨1⟩
    coprime := fun i => framedQuotientCoefficient_coprime q (U i) (hAffine i) (frames i)
    transition := units
    delta_transition := h0
    epsilon_transition := h1 }

/-- The morphism `X ⟶ ℙ¹_A` glued from the coordinates of the quotient in the given affine local
frames. -/
def fromSheafFrames {ι : Type v} {U : ι → X.Opens}
    (hAffine : ∀ i, IsAffineOpen (U i))
    (frames : ∀ i, N.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i)))
    (φ : A →+* Γ(X, ⊤)) (hU : IsOpenCover U) : X ⟶ ProjectiveLine.scheme A :=
  (sheafOpenPairData q hAffine frames).glue φ hU

@[reassoc] theorem restrict_fromSheafFrames {ι : Type v} {U : ι → X.Opens}
    (hAffine : ∀ i, IsAffineOpen (U i))
    (frames : ∀ i, N.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i)))
    (φ : A →+* Γ(X, ⊤)) (hU : IsOpenCover U) (i : ι) :
    (U i).ι ≫ fromSheafFrames q hAffine frames φ hU =
      ProjectiveLine.fromPair (ProjectiveLine.coefficientsOn φ (U i))
        (framedQuotientCoefficient q (U i) (frames i) ⟨0⟩)
        (framedQuotientCoefficient q (U i) (frames i) ⟨1⟩)
        (framedQuotientCoefficient_coprime q (U i) (hAffine i) (frames i)) :=
  (sheafOpenPairData q hAffine frames).restrict_glue φ hU i

@[reassoc] theorem fromSheafFrames_toSpec {ι : Type v} {U : ι → X.Opens}
    (hAffine : ∀ i, IsAffineOpen (U i))
    (frames : ∀ i, N.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i)))
    (φ : A →+* Γ(X, ⊤)) (hU : IsOpenCover U) :
    fromSheafFrames q hAffine frames φ hU ≫ ProjectiveLine.toSpec A =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) :=
  (sheafOpenPairData q hAffine frames).glue_toSpec φ hU

/-- Two independently framed affine opens agree on their intersection as full morphisms. -/
theorem sheafFramedPair_overlap (φ : A →+* Γ(X, ⊤)) (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (e' : N.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)) :
    X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫
        ProjectiveLine.fromPair (ProjectiveLine.coefficientsOn φ U)
          (framedQuotientCoefficient q U e ⟨0⟩) (framedQuotientCoefficient q U e ⟨1⟩)
          (framedQuotientCoefficient_coprime q U hU e) =
      X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫
        ProjectiveLine.fromPair (ProjectiveLine.coefficientsOn φ V)
          (framedQuotientCoefficient q V e' ⟨0⟩) (framedQuotientCoefficient q V e' ⟨1⟩)
          (framedQuotientCoefficient_coprime q V hV e') := by
  rw [ProjectiveLine.fromPair_naturality, ProjectiveLine.fromPair_naturality]
  simp only [ProjectiveLine.coefficientsOn_restrict]
  obtain ⟨unit, h0, h1⟩ := sheafFrames_overlap_common_unit q e e'
  simp only [h0, h1]
  exact ProjectiveLine.fromPair_unit_mul _ _ _
    ((framedQuotientCoefficient_coprime q V hV e').map
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V)).appTop.hom) unit

theorem fromSheafFrames_cover_independent {ι : Type v} {κ : Type w}
    {U : ι → X.Opens} {V : κ → X.Opens}
    (hAffineU : ∀ i, IsAffineOpen (U i)) (hAffineV : ∀ j, IsAffineOpen (V j))
    (framesU : ∀ i, N.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i)))
    (framesV : ∀ j, N.over (V j) ≅ SheafOfModules.unit (X.ringCatSheaf.over (V j)))
    (φ : A →+* Γ(X, ⊤)) (hU : IsOpenCover U) (hV : IsOpenCover V) :
    fromSheafFrames q hAffineU framesU φ hU = fromSheafFrames q hAffineV framesV φ hV := by
  apply (X.openCoverOfIsOpenCover _ (intersection_isOpenCover hU hV)).hom_ext
  rintro ⟨i, j⟩
  change (U i ⊓ V j).ι ≫ _ = (U i ⊓ V j).ι ≫ _
  conv_lhs =>
    rw [← X.homOfLE_ι (inf_le_left : U i ⊓ V j ≤ U i), Category.assoc,
      restrict_fromSheafFrames]
  conv_rhs =>
    rw [← X.homOfLE_ι (inf_le_right : U i ⊓ V j ≤ V j), Category.assoc,
      restrict_fromSheafFrames]
  exact sheafFramedPair_overlap q φ (U i) (V j) (hAffineU i) (hAffineV j)
    (framesU i) (framesV j)

/-- The glued morphism has the required formula in every affine local frame. -/
theorem fromSheafFrames_restrict_any {ι : Type v} {U : ι → X.Opens}
    (hAffine : ∀ i, IsAffineOpen (U i))
    (frames : ∀ i, N.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i)))
    (φ : A →+* Γ(X, ⊤)) (hU : IsOpenCover U)
    (V : X.Opens) (hV : IsAffineOpen V)
    (e : N.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)) :
    V.ι ≫ fromSheafFrames q hAffine frames φ hU =
      ProjectiveLine.fromPair (ProjectiveLine.coefficientsOn φ V)
        (framedQuotientCoefficient q V e ⟨0⟩) (framedQuotientCoefficient q V e ⟨1⟩)
        (framedQuotientCoefficient_coprime q V hV e) := by
  let W : Option ι → X.Opens := fun j => j.elim V U
  have hW : IsOpenCover W := by
    apply top_le_iff.mp
    intro x hx
    obtain ⟨i, hi⟩ := hU.exists_mem x
    exact Opens.mem_iSup.mpr ⟨some i, hi⟩
  let ha : ∀ j, IsAffineOpen (W j) := fun j => by cases j with
    | none => exact hV
    | some i => exact hAffine i
  let ef : ∀ j, N.over (W j) ≅ SheafOfModules.unit (X.ringCatSheaf.over (W j)) :=
    fun j => by cases j with
      | none => exact e
      | some i => exact frames i
  rw [fromSheafFrames_cover_independent q hAffine ha frames ef φ hU hW]
  exact restrict_fromSheafFrames q ha ef φ hW none

omit [N.IsQuasicoherent]

/-- The global Proj morphism of an ordered quotient line sheaf on a general scheme. -/
def fromQuotientLineSheaf
    (hline : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)))
    (φ : A →+* Γ(X, ⊤)) : X ⟶ ProjectiveLine.scheme A := by
  let := quotientLineSheaf_isQuasicoherent N hline
  let D := chooseAffineSheafFrameCover N hline
  exact fromSheafFrames q D.affine D.frame φ D.isOpenCover

@[reassoc] theorem fromQuotientLineSheaf_toSpec
    (hline : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)))
    (φ : A →+* Γ(X, ⊤)) :
    fromQuotientLineSheaf q hline φ ≫ ProjectiveLine.toSpec A =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) := by
  let := quotientLineSheaf_isQuasicoherent N hline
  unfold fromQuotientLineSheaf
  apply fromSheafFrames_toSpec

theorem lineSheaf_frame_coprime
    (hline : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)))
    (V : X.Opens) (hV : IsAffineOpen V)
    (e : N.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)) :
    IsCoprime (framedQuotientCoefficient q V e ⟨0⟩) (framedQuotientCoefficient q V e ⟨1⟩) := by
  let := quotientLineSheaf_isQuasicoherent N hline
  exact framedQuotientCoefficient_coprime q V hV e

/-- The global map recovers the ordered quotient coordinates in any affine frame. -/
@[reassoc] theorem fromQuotientLineSheaf_local_formula
    (hline : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)))
    (φ : A →+* Γ(X, ⊤)) (V : X.Opens) (hV : IsAffineOpen V)
    (e : N.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V)) :
    V.ι ≫ fromQuotientLineSheaf q hline φ =
      ProjectiveLine.fromPair (ProjectiveLine.coefficientsOn φ V)
        (framedQuotientCoefficient q V e ⟨0⟩) (framedQuotientCoefficient q V e ⟨1⟩)
        (lineSheaf_frame_coprime q hline V hV e) := by
  let := quotientLineSheaf_isQuasicoherent N hline
  unfold fromQuotientLineSheaf
  apply fromSheafFrames_restrict_any
  exact hV

end FlagVarieties.Foundations.QuotientPair
