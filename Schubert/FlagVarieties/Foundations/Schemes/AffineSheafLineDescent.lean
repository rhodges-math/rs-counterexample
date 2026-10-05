import Schubert.FlagVarieties.Foundations.Schemes.AffineSheafLocalProjective

/-!
# Descent from local sheaf trivializations to an affine quotient morphism

The hypotheses are isomorphisms of the sheaf over a principal
cover with the structure sheaf. Quasicoherence, frames of sections,
finite projectivity and rank one are all derived. For an ordered
quotient sheaf on any scheme, this produces its morphism to Proj on the
chosen affine chart. Refinement of arbitrary open trivializations to such a
principal cover is `Schemes/AffineSheafLineRefinement.lean`; the affine-chart
morphisms are glued in `Schemes/QuotientSheafProjectiveGluing.lean`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FlagVarieties.Foundations.QuotientPair

open AlgebraicGeometry CategoryTheory TensorProduct TopologicalSpace Opposite Limits

universe u

/-- Evaluate a local sheaf isomorphism on the terminal object of its open site. -/
def overSheafSectionFrame {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Γ(M, U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  ((SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))).mapIso e).toLinearEquiv

variable {R : CommRingCat.{u}} (M : (Spec R).Modules) (s : Set R)
  (hcover : IsOpenCover (fun g : s => PrimeSpectrum.basicOpen (g : R)))
  (e : ∀ g : s, M.over (PrimeSpectrum.basicOpen (g : R)) ≅
    SheafOfModules.unit ((Spec R).ringCatSheaf.over (PrimeSpectrum.basicOpen (g : R))))

include hcover e

/-- Quasicoherence follows from local line-sheaf trivializations. -/
theorem isQuasicoherent_of_principal_sheaf_frames : M.IsQuasicoherent := by
  let (g : s) : (M.over (PrimeSpectrum.basicOpen (g : R))).IsQuasicoherent := by
    let S := (Spec R).ringCatSheaf.over (PrimeSpectrum.basicOpen (g : R))
    let eu : SheafOfModules.free (R := S) (ULift.{u} Unit) ≅ SheafOfModules.unit S :=
      coproductUniqueIso (fun _ : ULift.{u} Unit => SheafOfModules.unit S)
    exact (SheafOfModules.isQuasicoherent S).prop_of_iso (eu ≪≫ (e g).symm) inferInstance
  apply SheafOfModules.IsQuasicoherent.of_coversTop M
    (fun g : s => PrimeSpectrum.basicOpen (g : R))
  simpa only [Opens.coversTop_iff] using hcover

/-- The affine section module of the locally trivial line sheaf is finite projective. -/
theorem finite_projective_of_principal_sheaf_frames :
    Module.Finite R (sheafGlobalModule M) ∧ Module.Projective R (sheafGlobalModule M) := by
  let := isQuasicoherent_of_principal_sheaf_frames M s hcover e
  let frames := fun g : s => overSheafSectionFrame M _ (e g)
  exact ⟨sheafGlobal_finite_of_principal_frames M s hcover frames,
    sheafGlobal_projective_of_principal_frames M s hcover frames⟩

/-- The rank-one condition is derived, rather than included in the presentation data. -/
theorem rank_one_of_principal_sheaf_frames (p : PrimeSpectrum R) :
    Module.rankAtStalk (sheafGlobalModule M) p = 1 := by
  let := isQuasicoherent_of_principal_sheaf_frames M s hcover e
  exact sheafGlobal_rank_one_of_principal_frames M s hcover
    (fun g : s => overSheafSectionFrame M _ (e g)) p

omit hcover e

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : Spec R ⟶ X)
  [IsOpenImmersion f] {N : X.Modules}

/-- A quotient line sheaf yields its relative projective morphism on this affine chart. -/
def fromAffineQuotientSheafLocalFrames (φ : A →+* R)
    (q : orderedFreeSheaf X ⟶ N) [Epi q]
    (s : Set R) (hcover : IsOpenCover (fun g : s => PrimeSpectrum.basicOpen (g : R)))
    (e : ∀ g : s, (N.restrict f).over (PrimeSpectrum.basicOpen (g : R)) ≅
      SheafOfModules.unit ((Spec R).ringCatSheaf.over (PrimeSpectrum.basicOpen (g : R)))) :
    Spec R ⟶ ProjectiveLine.scheme A := by
  let := isQuasicoherent_of_principal_sheaf_frames (N.restrict f) s hcover e
  let := (finite_projective_of_principal_sheaf_frames (N.restrict f) s hcover e).1
  let := (finite_projective_of_principal_sheaf_frames (N.restrict f) s hcover e).2
  exact fromFiniteProjectivePairOver (sheafGlobalModule (N.restrict f))
    (rank_one_of_principal_sheaf_frames (N.restrict f) s hcover e) φ
    (affineQuotientSectionPair f q)
    (sheafQuotientPair_surjective (affineQuotientSheafMap f q))

theorem fromAffineQuotientSheafLocalFrames_toSpec (φ : A →+* R)
    (q : orderedFreeSheaf X ⟶ N) [Epi q]
    (s : Set R) (hcover : IsOpenCover (fun g : s => PrimeSpectrum.basicOpen (g : R)))
    (e : ∀ g : s, (N.restrict f).over (PrimeSpectrum.basicOpen (g : R)) ≅
      SheafOfModules.unit ((Spec R).ringCatSheaf.over (PrimeSpectrum.basicOpen (g : R)))) :
    fromAffineQuotientSheafLocalFrames f φ q s hcover e ≫ ProjectiveLine.toSpec A =
      Spec.map (CommRingCat.ofHom φ) := by
  let := isQuasicoherent_of_principal_sheaf_frames (N.restrict f) s hcover e
  let := (finite_projective_of_principal_sheaf_frames (N.restrict f) s hcover e).1
  let := (finite_projective_of_principal_sheaf_frames (N.restrict f) s hcover e).2
  unfold fromAffineQuotientSheafLocalFrames
  apply fromFiniteProjectivePairOver_toSpec

/-- The chart morphism depends only on the quotient, not the principal cover or local sheaf
frames. -/
theorem fromAffineQuotientSheafLocalFrames_independent (φ : A →+* R)
    (q : orderedFreeSheaf X ⟶ N) [Epi q]
    (s t : Set R)
    (hs : IsOpenCover (fun g : s => PrimeSpectrum.basicOpen (g : R)))
    (ht : IsOpenCover (fun g : t => PrimeSpectrum.basicOpen (g : R)))
    (e : ∀ g : s, (N.restrict f).over (PrimeSpectrum.basicOpen (g : R)) ≅
      SheafOfModules.unit ((Spec R).ringCatSheaf.over (PrimeSpectrum.basicOpen (g : R))))
    (e' : ∀ g : t, (N.restrict f).over (PrimeSpectrum.basicOpen (g : R)) ≅
      SheafOfModules.unit ((Spec R).ringCatSheaf.over (PrimeSpectrum.basicOpen (g : R)))) :
    fromAffineQuotientSheafLocalFrames f φ q s hs e =
      fromAffineQuotientSheafLocalFrames f φ q t ht e' := by
  rfl

end FlagVarieties.Foundations.QuotientPair
