import RSCounterexample.FlagVarieties.Foundations.Schemes.SelectedChartPointFaithfulness

/-! # Recovering exact algebra maps from affine scheme points -/

noncomputable section

namespace FlagVarieties.Foundations.QuotientCharts

open AlgebraicGeometry CategoryTheory

universe u
variable (R : Type u) [CommRing R]
  {A B K : Type u} [CommRing A] [CommRing B] [CommRing K]
  [Algebra R A] [Algebra R B]

/-- A scheme morphism of affine spectra over the base is the unique
`R`-algebra homomorphism obtained from `Spec.preimage`. -/
def affinePointAlgebraHom [Algebra R K]
    (p : Spec (.of K) ⟶ Spec (.of A))
    (hp : p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R K))) : A →ₐ[R] K :=
  { (Spec.preimage p).hom with
    commutes' := fun x => RingHom.congr_fun
      (spec_preimage_comp_eq (algebraMap R A) p (algebraMap R K) hp) x }

@[reassoc] theorem affinePointAlgebraHom_spec [Algebra R K]
    (p : Spec (.of K) ⟶ Spec (.of A))
    (hp : p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    Spec.map (CommRingCat.ofHom (affinePointAlgebraHom R p hp).toRingHom) = p :=
  Spec.map_preimage p

theorem affinePointAlgebraHom_unique [Algebra R K]
    (p : Spec (.of K) ⟶ Spec (.of A))
    (hp : p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R K)))
    (f : A →ₐ[R] K)
    (hf : Spec.map (CommRingCat.ofHom f.toRingHom) = p) :
    f = affinePointAlgebraHom R p hp := by
  apply AlgHom.ext
  intro x
  have he := Spec.map_injective
    (hf.trans (affinePointAlgebraHom_spec R p hp).symm)
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom he) x

/-- The shared map to `Spec R` determines the coefficient algebra
for two affine points without a prior `R`-algebra instance on `K`. -/
@[instance_reducible] def affinePointPairAlgebra
    (p : Spec (.of K) ⟶ Spec (.of A))
    (q : Spec (.of K) ⟶ Spec (.of B))
    (_h : p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))) : Algebra R K :=
  ((Spec.fullyFaithful.preimage
    (p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)))).unop.hom).toAlgebra

theorem affinePointPairAlgebra_spec
    (p : Spec (.of K) ⟶ Spec (.of A))
    (q : Spec (.of K) ⟶ Spec (.of B))
    (h : p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    letI : Algebra R K := affinePointPairAlgebra R p q h
    Spec.map (CommRingCat.ofHom (algebraMap R K)) =
      p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  change Spec.map (Spec.fullyFaithful.preimage
    (p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)))).unop = _
  exact Spec.map_preimage_unop _

/-- First original affine map as a homomorphism over the recovered common
coefficient algebra. -/
def affinePointPairLeftHom
    (p : Spec (.of K) ⟶ Spec (.of A))
    (q : Spec (.of K) ⟶ Spec (.of B))
    (h : p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    letI : Algebra R K := affinePointPairAlgebra R p q h
    A →ₐ[R] K := by
  letI : Algebra R K := affinePointPairAlgebra R p q h
  exact affinePointAlgebraHom R p (affinePointPairAlgebra_spec R p q h).symm

/-- Second original affine map over exactly the same coefficient algebra. -/
def affinePointPairRightHom
    (p : Spec (.of K) ⟶ Spec (.of A))
    (q : Spec (.of K) ⟶ Spec (.of B))
    (h : p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    letI : Algebra R K := affinePointPairAlgebra R p q h
    B →ₐ[R] K := by
  letI : Algebra R K := affinePointPairAlgebra R p q h
  apply affinePointAlgebraHom R q
  exact h.symm.trans (affinePointPairAlgebra_spec R p q h).symm

@[reassoc] theorem affinePointPairLeftHom_spec
    (p : Spec (.of K) ⟶ Spec (.of A))
    (q : Spec (.of K) ⟶ Spec (.of B))
    (h : p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    letI : Algebra R K := affinePointPairAlgebra R p q h
    Spec.map (CommRingCat.ofHom (affinePointPairLeftHom R p q h).toRingHom) = p := by
  change Spec.map (Spec.preimage p) = p
  exact Spec.map_preimage p

@[reassoc] theorem affinePointPairRightHom_spec
    (p : Spec (.of K) ⟶ Spec (.of A))
    (q : Spec (.of K) ⟶ Spec (.of B))
    (h : p ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      q ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    letI : Algebra R K := affinePointPairAlgebra R p q h
    Spec.map (CommRingCat.ofHom (affinePointPairRightHom R p q h).toRingHom) = q := by
  change Spec.map (Spec.preimage q) = q
  exact Spec.map_preimage q

end FlagVarieties.Foundations.QuotientCharts
