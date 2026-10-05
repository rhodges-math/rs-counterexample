import Schubert.FlagVarieties.Foundations.Schemes.AffineSheafLineDescent

/-!
# Principal refinement of local line-sheaf trivializations

Local trivializations are isomorphisms in mathlib's sheaf category
over open subsets. They restrict to smaller opens by the canonical
`overMap` functor. The principal basis of an affine scheme then supplies
the cover and local frames used in the finite-projectivity descent.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TensorProduct TopologicalSpace Opposite

universe u

/-- A local sheaf trivialization restricts along an open inclusion. -/
def restrictOverSheafFrame {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V) :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).app M).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf (homOfLE h)).mapIso e ≪≫
    SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) (homOfLE h)

variable {R : CommRingCat.{u}} (M : (Spec R).Modules)

/-- Arbitrary local trivializations yield a principal trivializing cover. -/
theorem exists_principal_sheaf_frames
    (hline : ∀ p : Spec R, ∃ U : (Spec R).Opens, p ∈ U ∧
      Nonempty (M.over U ≅ SheafOfModules.unit ((Spec R).ringCatSheaf.over U))) :
    ∃ s : Set R,
      IsOpenCover (fun g : s => PrimeSpectrum.basicOpen (g : R)) ∧
      Nonempty (∀ g : s, M.over (PrimeSpectrum.basicOpen (g : R)) ≅
        SheafOfModules.unit ((Spec R).ringCatSheaf.over (PrimeSpectrum.basicOpen (g : R)))) := by
  let s : Set R := {g | Nonempty (M.over (PrimeSpectrum.basicOpen g) ≅
    SheafOfModules.unit ((Spec R).ringCatSheaf.over (PrimeSpectrum.basicOpen g)))}
  refine ⟨s, ?_, ⟨fun g => g.property.some⟩⟩
  apply top_le_iff.mp
  intro p hp
  obtain ⟨U, hpU, ⟨e⟩⟩ := hline p
  obtain ⟨a, ⟨_, ⟨g, rfl⟩, rfl⟩, hpg, hgU : PrimeSpectrum.basicOpen g ≤ U⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hpU U.2
  exact Opens.mem_iSup.mpr ⟨⟨g, ⟨restrictOverSheafFrame M hgU e⟩⟩, hpg⟩

/-- A locally trivial line sheaf on an affine scheme has finite projective sections. -/
theorem locally_trivial_sheaf_finite_projective
    (hline : ∀ p : Spec R, ∃ U : (Spec R).Opens, p ∈ U ∧
      Nonempty (M.over U ≅ SheafOfModules.unit ((Spec R).ringCatSheaf.over U))) :
    Module.Finite R (sheafGlobalModule M) ∧ Module.Projective R (sheafGlobalModule M) := by
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_principal_sheaf_frames M hline
  exact finite_projective_of_principal_sheaf_frames M s hs e

theorem locally_trivial_sheaf_rank_one
    (hline : ∀ p : Spec R, ∃ U : (Spec R).Opens, p ∈ U ∧
      Nonempty (M.over U ≅ SheafOfModules.unit ((Spec R).ringCatSheaf.over U)))
    (p : PrimeSpectrum R) : Module.rankAtStalk (sheafGlobalModule M) p = 1 := by
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_principal_sheaf_frames M hline
  exact rank_one_of_principal_sheaf_frames M s hs e p

theorem locally_trivial_sheaf_isQuasicoherent
    (hline : ∀ p : Spec R, ∃ U : (Spec R).Opens, p ∈ U ∧
      Nonempty (M.over U ≅ SheafOfModules.unit ((Spec R).ringCatSheaf.over U))) :
    M.IsQuasicoherent := by
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_principal_sheaf_frames M hline
  exact isQuasicoherent_of_principal_sheaf_frames M s hs e

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : Spec R ⟶ X)
  [IsOpenImmersion f] {N : X.Modules}

/-- A quotient line sheaf supplies its affine Proj morphism without a supplied cover or frames. -/
def fromAffineQuotientLineSheaf (φ : A →+* R) (q : orderedFreeSheaf X ⟶ N) [Epi q]
    (hline : ∀ p : Spec R, ∃ U : (Spec R).Opens, p ∈ U ∧
      Nonempty ((N.restrict f).over U ≅ SheafOfModules.unit ((Spec R).ringCatSheaf.over U))) :
    Spec R ⟶ ProjectiveLine.scheme A := by
  let := locally_trivial_sheaf_isQuasicoherent (N.restrict f) hline
  let := (locally_trivial_sheaf_finite_projective (N.restrict f) hline).1
  let := (locally_trivial_sheaf_finite_projective (N.restrict f) hline).2
  exact fromFiniteProjectivePairOver (sheafGlobalModule (N.restrict f))
    (locally_trivial_sheaf_rank_one (N.restrict f) hline) φ
    (affineQuotientSectionPair f q)
    (sheafQuotientPair_surjective (affineQuotientSheafMap f q))

theorem fromAffineQuotientLineSheaf_toSpec (φ : A →+* R)
    (q : orderedFreeSheaf X ⟶ N) [Epi q]
    (hline : ∀ p : Spec R, ∃ U : (Spec R).Opens, p ∈ U ∧
      Nonempty ((N.restrict f).over U ≅ SheafOfModules.unit ((Spec R).ringCatSheaf.over U))) :
    fromAffineQuotientLineSheaf f φ q hline ≫ ProjectiveLine.toSpec A =
      Spec.map (CommRingCat.ofHom φ) := by
  let := locally_trivial_sheaf_isQuasicoherent (N.restrict f) hline
  let := (locally_trivial_sheaf_finite_projective (N.restrict f) hline).1
  let := (locally_trivial_sheaf_finite_projective (N.restrict f) hline).2
  unfold fromAffineQuotientLineSheaf
  apply fromFiniteProjectivePairOver_toSpec

/-- The cover-free constructor agrees with construction using any principal sheaf frames. -/
theorem fromAffineQuotientLineSheaf_eq_localFrames (φ : A →+* R)
    (q : orderedFreeSheaf X ⟶ N) [Epi q]
    (hline : ∀ p : Spec R, ∃ U : (Spec R).Opens, p ∈ U ∧
      Nonempty ((N.restrict f).over U ≅ SheafOfModules.unit ((Spec R).ringCatSheaf.over U)))
    (s : Set R) (hs : IsOpenCover (fun g : s => PrimeSpectrum.basicOpen (g : R)))
    (e : ∀ g : s, (N.restrict f).over (PrimeSpectrum.basicOpen (g : R)) ≅
      SheafOfModules.unit ((Spec R).ringCatSheaf.over (PrimeSpectrum.basicOpen (g : R)))) :
    fromAffineQuotientLineSheaf f φ q hline =
      fromAffineQuotientSheafLocalFrames f φ q s hs e := by
  rfl

end FlagVarieties.Foundations.QuotientPair
