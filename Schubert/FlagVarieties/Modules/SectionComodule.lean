import Schubert.FlagVarieties.LineBundle.BorelRep
import Schubert.FlagVarieties.LineBundle.BorelFlat
import Schubert.GLRep.Borel.BorelRational
import TauCeti.Algebra.HopfAlgebra.Antipode
import TauCeti.Algebra.Coalgebra.Subcomodule.Induced

/-!
# The algebraic-group form of the action of `B` on `H⁰(X, 𝓛(η))`

Over any commutative ring `R`, let `H = 𝒪(GL_n)` and `C = 𝒪(B)` (Tau Ceti's coordinate Hopf
algebras `GeneralLinear.coordinateHopfAlgebra`, `UpperTriangular.coordinateHopfAlgebra`; `π : H → C`
the restriction). Left translation `(b · f)(g) = f(b⁻¹ g)` is the right coaction

  `λ = (id ⊗ π) ∘ τ ∘ (S ⊗ id) ∘ Δ : H → H ⊗ C`, `λ(x_ij) = Σ_k x_kj ⊗ π(S x_ik)`

(`FlagVarieties.leftCoaction`, on `GLCoord R n`: `FlagVarieties.leftCoactionGL`), a comodule
structure (`FlagVarieties.leftComodule`, `FlagVarieties.glLeftRegularComodule`); contracting it with
a point `b ∈ B(R)` gives `GLRep.leftTranslHom b` (`FlagVarieties.contract_glLeftRegularComodule`).

* **Closed subschemes stable under `B`.** An ideal `J` is stable under the coaction,
  `λ(J) ⊆ J ⊗ C` (`FlagVarieties.IsLeftCoactionStable`), iff `λ(J)` vanishes in `(H/J) ⊗ C`
  (`isLeftCoactionStable_iff`, by right exactness); it suffices to check generators
  (`isLeftCoactionStable_of_span`); it implies stability under `B(R)`
  (`IsLeftCoactionStable.isLeftTranslStable`), and over an infinite field the two are equivalent
  (`isLeftCoactionStable_iff_isLeftTranslStable`, since `B(K)` separates `M ⊗ C`,
  `tensor_ext_borelPoint`). Then `H/J` is a comodule (`FlagVarieties.quotComodule`) whose point
  action is `leftTranslQuot` (`contract_quotComodule`).
* **Semi-invariants.** Left and right translations commute (`rightCoactionMod_comm`), so the
  coaction commutes with the defect `f ↦ ρ(f) − f ⊗ η⁻¹`
  (`rTensor_semiInvariantDefect_leftCoactionGL`)
  and, `C` being flat over every `R` (`instFlatBorelHopf`, from `instFlatBorelCoord`), preserves
  `(H/J)^{(B, η)}`
  (`leftCoactionQuot_mem_range`): `FlagVarieties.semiInvariantsComodule`, with point action
  `semiInvariantsRep` (`contract_semiInvariantsComodule`).
* **`H⁰(X, 𝓛(η))`.** Transported through `sectionsEquivSemiInvariants`,
  **`FlagVarieties.sectionsComodule`**, with point action `sectionsRep`
  (`contract_sectionsComodule`).
* **Over a field `K`:** a finite-dimensional comodule gives a rational representation of `B(K)`
  (`isRationalBorelRep_of_contract`, `isRationalBorelRep_sectionsRep`), and over an infinite field
  the comodule is determined by its point action (`comodule_ext_of_contract`,
  `eq_sectionsComodule_iff`).

The geometric description of the coaction as the pullback along the action `B × X → X` is a
follow-up (it needs the action morphism on `X` and the comparison of its comorphism with `λ`).
-/

open TauCeti TauCeti.GeneralLinear
open GLRep (glHopf borelHopf)
open scoped TensorProduct

namespace FlagVarieties

noncomputable section

/-! ### Descent and transport of comodule structures -/

section Descent

variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M Q : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid Q] [Module R Q]

omit [Coalgebra R C] in
theorem lTensor_rTensor_comm {D : Type*} [AddCommMonoid D] [Module R D] (f : C →ₗ[R] D)
    (q : M →ₗ[R] Q) (t : M ⊗[R] C) :
    f.lTensor Q (q.rTensor C t) = q.rTensor D (f.lTensor M t) :=
  (LinearMap.congr_fun (LinearMap.lTensor_comp_rTensor (f := q) (g := f)) t).trans
    (LinearMap.congr_fun (LinearMap.rTensor_comp_lTensor (f := q) (g := f)) t).symm

/-- **Descent of a comodule structure along a surjection**: a linear map `coact : Q → Q ⊗ C`
compatible with the coaction of `M` along a surjective linear map `q : M → Q` is a comodule
structure on `Q`. -/
@[instance_reducible]
def comoduleOfSurjective [TauCeti.Comodule R C M] (q : M →ₗ[R] Q) (hq : Function.Surjective q)
    (coact : Q →ₗ[R] Q ⊗[R] C)
    (h : ∀ m, coact (q m) = q.rTensor C (TauCeti.Comodule.coact (R := R) (C := C) m)) :
    TauCeti.Comodule R C Q where
  coact := coact
  coassoc := LinearMap.ext fun x => by
    obtain ⟨m, rfl⟩ := hq x
    have hc : coact ∘ₗ q = q.rTensor C ∘ₗ TauCeti.Comodule.coact (R := R) (C := C) (M := M) :=
      LinearMap.ext h
    set t := TauCeti.Comodule.coact (R := R) (C := C) (M := M) m
    change TensorProduct.assoc R Q C C (coact.rTensor C (coact (q m))) =
      Coalgebra.comul.lTensor Q (coact (q m))
    rw [h, ← LinearMap.rTensor_comp_apply, hc, LinearMap.rTensor_comp_apply]
    change TensorProduct.assoc R Q C C (TensorProduct.map (TensorProduct.map q LinearMap.id)
      LinearMap.id ((TauCeti.Comodule.coact (R := R) (C := C) (M := M)).rTensor C t)) = _
    rw [← TensorProduct.map_map_assoc, TauCeti.Comodule.coassoc_apply, TensorProduct.map_id]
    exact (lTensor_rTensor_comm _ q t).symm
  lTensor_counit_comp_coact := LinearMap.ext fun x => by
    obtain ⟨m, rfl⟩ := hq x
    change Coalgebra.counit.lTensor Q (coact (q m)) = q m ⊗ₜ[R] 1
    rw [h, lTensor_rTensor_comm, TauCeti.Comodule.lTensor_counit_coact, LinearMap.rTensor_tmul]

/-- Transport of a comodule structure along a linear equivalence `e`, with coaction
`(e ⊗ id) ∘ ρ ∘ e⁻¹` (the construction of Tau Ceti's `Comodule.Transport`). -/
@[instance_reducible]
def transportComodule [TauCeti.Comodule R C M] (e : M ≃ₗ[R] Q) : TauCeti.Comodule R C Q :=
  comoduleOfSurjective e.toLinearMap e.surjective
    (e.toLinearMap.rTensor C ∘ₗ TauCeti.Comodule.coact (R := R) (C := C) (M := M) ∘ₗ
      e.symm.toLinearMap)
    fun m => congrArg (fun z => e.toLinearMap.rTensor C
      (TauCeti.Comodule.coact (R := R) (C := C) (M := M) z)) (e.symm_apply_apply m)

end Descent

section Contraction

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Bialgebra R S]
variable {M Q : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid Q] [Module R Q]

theorem rid_lTensor_rTensor_comm (x : S →ₗ[R] R) (q : M →ₗ[R] Q) (t : M ⊗[R] S) :
    TensorProduct.rid R Q (x.lTensor Q (q.rTensor S t)) =
      q (TensorProduct.rid R M (x.lTensor M t)) := by
  induction t with
  | tmul m c => simp
  | add s t hs ht => simp only [map_add, hs, ht]

/-- Contracting a descended coaction with a point. -/
theorem contract_comoduleOfSurjective [TauCeti.Comodule R S M] (q : M →ₗ[R] Q)
    (coact : Q →ₗ[R] Q ⊗[R] S)
    (h : ∀ m, coact (q m) = q.rTensor S (TauCeti.Comodule.coact (R := R) (C := S) m))
    (x : S →ₐ[R] R) (m : M) :
    GLRep.contract x coact (q m) =
      q (GLRep.contract x (TauCeti.Comodule.coact (R := R) (C := S) (M := M)) m) := by
  change TensorProduct.rid R Q (x.toLinearMap.lTensor Q (coact (q m))) =
    q (TensorProduct.rid R M (x.toLinearMap.lTensor M _))
  rw [h, rid_lTensor_rTensor_comm]

/-- Contracting a transported coaction with a point: `e ∘ (contraction) ∘ e⁻¹`. -/
theorem contract_transportComodule [TauCeti.Comodule R S M] (e : M ≃ₗ[R] Q) (x : S →ₐ[R] R)
    (y : Q) :
    GLRep.contract x (transportComodule (C := S) e).coact y =
      e (GLRep.contract x (TauCeti.Comodule.coact (R := R) (C := S) (M := M)) (e.symm y)) := by
  conv_lhs => rw [← e.apply_symm_apply y]
  exact contract_comoduleOfSurjective e.toLinearMap _
    (fun m => congrArg (fun z => e.toLinearMap.rTensor S
      (TauCeti.Comodule.coact (R := R) (C := S) (M := M) z)) (e.symm_apply_apply m)) x (e.symm y)

/-- The point action on a subcomodule is the restriction of the ambient point action. -/
theorem coe_contract_subcomodule' [Module.Flat R S] [TauCeti.Comodule R S M]
    (N : TauCeti.Subcomodule R S M) (x : S →ₐ[R] R) (u : N) :
    ((GLRep.contract x (TauCeti.Comodule.coact (R := R) (C := S) (M := N)) u : N) : M) =
      GLRep.contract x (TauCeti.Comodule.coact (R := R) (C := S) (M := M)) u := by
  change SMulMemClass.subtype N (TensorProduct.rid R N (x.toLinearMap.lTensor N
      (TauCeti.Comodule.coact (R := R) (C := S) (M := N) u))) = _
  rw [← rid_lTensor_rTensor_comm, TauCeti.Subcomodule.subtype_rTensor_coact]
  rfl

end Contraction

variable (R : Type*) [CommRing R] (n : ℕ)

/-- The restriction `π : 𝒪(GL_n) → 𝒪(B)`, an algebra map. -/
abbrev restrictToBorel : glHopf R n →ₐ[R] borelHopf R n :=
    (UpperTriangular.coordinateMap R n).hom.toAlgHom

/-- **The left-translation coaction** `λ = (id ⊗ π) ∘ τ ∘ (S ⊗ id) ∘ Δ`:
`(b · f)(g) = f(b⁻¹ g)`. -/
def leftCoaction : glHopf R n →ₐ[R] glHopf R n ⊗[R] borelHopf R n :=
  (Algebra.TensorProduct.map (AlgHom.id R (glHopf R n)) (restrictToBorel R n)).comp
    ((Algebra.TensorProduct.comm R (glHopf R n) (glHopf R n)).toAlgHom.comp
      ((Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom R (glHopf R n))
        (AlgHom.id R (glHopf R n))).comp (Bialgebra.comulAlgHom R (glHopf R n))))

/-- The coordinate `x_ij` of `𝒪(GL_n)`. -/
def genericEntry (i j : Fin n) : glHopf R n := GeneralLinear.genericMatrix R n i j

variable {R n}

theorem genericEntry_eq (i j : Fin n) :
    genericEntry R n i j =
      coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n (MvPolynomial.X (i, j))) :=
  GeneralLinear.genericMatrix_apply R n i j

/-! ### `𝒪(B)` is flat over every `R` -/

variable (R n) in
/-- Tau Ceti's `𝒪(B)` to `BorelCoord R n` (the same quotient of `𝒪(GL_n)`). -/
def borelHopfToBorelCoord : borelHopf R n →ₐ[R] BorelCoord R n :=
  Ideal.Quotient.liftₐ (UpperTriangular.definingHopfIdeal R n).toIdeal
    ((Ideal.Quotient.mkₐ R (borelCoordIdeal R n)).comp
      (coordinateHopfAlgebraAlgEquiv R n).symm.toAlgHom) fun a ha =>
    UpperTriangular.definingHopfIdeal_toIdeal_le_ker R n _ (fun i j hji => by
      change Ideal.Quotient.mk (borelCoordIdeal R n)
          (coordinateRingMap R n (MvPolynomial.X (i, j))) = 0
      rw [← localizedGenericMatrix_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨⟨(i, j), hji⟩, rfl⟩) ha

variable (R n) in
/-- `BorelCoord R n` to Tau Ceti's `𝒪(B)`. -/
def borelCoordToBorelHopf : BorelCoord R n →ₐ[R] borelHopf R n :=
  Ideal.Quotient.liftₐ (borelCoordIdeal R n)
    ((restrictToBorel R n).comp (coordinateHopfAlgebraAlgEquiv R n).toAlgHom) fun a ha => by
    have hle : borelCoordIdeal R n ≤
        RingHom.ker
          ((restrictToBorel R n).comp (coordinateHopfAlgebraAlgEquiv R n).toAlgHom).toRingHom := by
      rw [borelCoordIdeal, Ideal.span_le]
      rintro _ ⟨⟨⟨i, j⟩, hij⟩, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      change (UpperTriangular.coordinateMap R n).hom (genericEntry R n i j) = 0
      rw [UpperTriangular.coordinateMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem, UpperTriangular.definingHopfIdeal_toIdeal]
      exact Ideal.subset_span ⟨i, j, hij, genericEntry_eq i j⟩
    exact hle ha

theorem borelCoordToBorelHopf_comp_borelHopfToBorelCoord :
    (borelCoordToBorelHopf R n).comp (borelHopfToBorelCoord R n) = AlgHom.id R (borelHopf R n) := by
  have h : ((borelCoordToBorelHopf R n).comp (borelHopfToBorelCoord R n)).comp
      (restrictToBorel R n) = restrictToBorel R n :=
    coordinateHopfAlgebra_algHom_ext R n fun i j => rfl
  refine AlgHom.ext fun c => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
  exact DFunLike.congr_fun h x

/-- **`𝒪(B)` is flat over every commutative ring `R`**: it is a retract of `BorelCoord R n`,
which is flat (`FlagVarieties.instFlatBorelCoord`). -/
instance instFlatBorelHopf : Module.Flat R (UpperTriangular.coordinateHopfAlgebra R n) :=
  Module.Flat.of_retract (borelHopfToBorelCoord R n).toLinearMap
      (borelCoordToBorelHopf R n).toLinearMap
    (LinearMap.ext fun x => by
      change ((borelCoordToBorelHopf R n).comp (borelHopfToBorelCoord R n)) x = x
      rw [borelCoordToBorelHopf_comp_borelHopfToBorelCoord, AlgHom.id_apply])

theorem comul_genericEntry (i j : Fin n) :
    Coalgebra.comul (R := R) (genericEntry R n i j) = ∑ k,
        genericEntry R n i k ⊗ₜ[R] genericEntry R n k j := by
  rw [genericEntry_eq, coordinateHopfAlgebra_comul_X]
  simp only [genericEntry_eq]

/-- `λ(x_ij) = Σ_k x_kj ⊗ π(S x_ik)`. -/
theorem leftCoaction_genericEntry (i j : Fin n) :
    leftCoaction R n (genericEntry R n i j) =
      ∑ k, genericEntry R n k j ⊗ₜ[R]
        restrictToBorel R n (HopfAlgebra.antipode R (genericEntry R n i k)) := by
  rw [leftCoaction, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply,
    Bialgebra.comulAlgHom_apply, comul_genericEntry, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem comul_restrictToBorel_antipode (i k : Fin n) :
    Coalgebra.comul (R := R) (restrictToBorel R n (HopfAlgebra.antipode R (genericEntry R n i k))) =
      ∑ l, restrictToBorel R n (HopfAlgebra.antipode R (genericEntry R n l k)) ⊗ₜ[R]
        restrictToBorel R n (HopfAlgebra.antipode R (genericEntry R n i l)) := by
  change Coalgebra.comul (R := R) ((UpperTriangular.coordinateMap R n).hom
    (HopfAlgebra.antipode R (genericEntry R n i k))) = _
  rw [← CoalgHomClass.map_comp_comul_apply, HopfAlgebra.antipode_comul_antidistrib_apply,
    comul_genericEntry, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [TensorProduct.comm_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul]
  rfl

theorem counit_restrictToBorel_antipode (i k : Fin n) :
    Coalgebra.counit (R := R)
        (restrictToBorel R n (HopfAlgebra.antipode R (genericEntry R n i k))) =
      if i = k then 1 else 0 := by
  change Coalgebra.counit (R := R) ((UpperTriangular.coordinateMap R n).hom
    (HopfAlgebra.antipode R (genericEntry R n i k))) = _
  rw [CoalgHomClass.counit_comp_apply, HopfAlgebra.counit_antipode, genericEntry_eq,
    coordinateHopfAlgebra_counit_X]

theorem leftCoaction_coassoc :
    ((Algebra.TensorProduct.assoc R R R (glHopf R n) (borelHopf R n) (borelHopf R n)).toAlgHom.comp
        ((Algebra.TensorProduct.map (leftCoaction R n) (AlgHom.id R (borelHopf R n))).comp
          (leftCoaction R n))) =
      (Algebra.TensorProduct.map (AlgHom.id R (glHopf R n))
          (Bialgebra.comulAlgHom R (borelHopf R n))).comp
        (leftCoaction R n) := by
  refine coordinateHopfAlgebra_algHom_ext R n fun i j => ?_
  rw [← genericEntry_eq, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply,
      leftCoaction_genericEntry,
    map_sum, map_sum, map_sum]
  have hL : ∀ k, (Algebra.TensorProduct.assoc R R R (glHopf R n) (borelHopf R n) (borelHopf R n))
      ((Algebra.TensorProduct.map (leftCoaction R n) (AlgHom.id R (borelHopf R n)))
        (genericEntry R n k j ⊗ₜ[R] restrictToBorel R n
            (HopfAlgebra.antipode R (genericEntry R n i k)))) =
      ∑ l, genericEntry R n l j ⊗ₜ[R]
          (restrictToBorel R n (HopfAlgebra.antipode R (genericEntry R n k l)) ⊗ₜ[R]
        restrictToBorel R n (HopfAlgebra.antipode R (genericEntry R n i k))) := by
    intro k
    rw [Algebra.TensorProduct.map_tmul, leftCoaction_genericEntry, TensorProduct.sum_tmul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [AlgHom.id_apply]
    rfl
  have hR : ∀ k, (Algebra.TensorProduct.map (AlgHom.id R (glHopf R n))
      (Bialgebra.comulAlgHom R (borelHopf R n)))
        (genericEntry R n k j ⊗ₜ[R] restrictToBorel R n
            (HopfAlgebra.antipode R (genericEntry R n i k))) =
      ∑ l, genericEntry R n k j ⊗ₜ[R]
          (restrictToBorel R n (HopfAlgebra.antipode R (genericEntry R n l k)) ⊗ₜ[R]
        restrictToBorel R n (HopfAlgebra.antipode R (genericEntry R n i l))) := by
    intro k
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Bialgebra.comulAlgHom_apply,
      comul_restrictToBorel_antipode, TensorProduct.tmul_sum]
  exact (Finset.sum_congr rfl fun k _ => hL k).trans
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun k _ => (hR k).symm))

theorem leftCoaction_counit :
    (Algebra.TensorProduct.map (AlgHom.id R (glHopf R n))
        (Bialgebra.counitAlgHom R (borelHopf R n))).comp
        (leftCoaction R n) = Algebra.TensorProduct.includeLeft := by
  classical
  refine coordinateHopfAlgebra_algHom_ext R n fun i j => ?_
  rw [← genericEntry_eq, AlgHom.comp_apply, leftCoaction_genericEntry, map_sum,
    Algebra.TensorProduct.includeLeft_apply, Finset.sum_eq_single i]
  · rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Bialgebra.counitAlgHom_apply,
      counit_restrictToBorel_antipode, ite_eq_left_iff.mpr fun h => absurd rfl h]
  · intro k _ hk
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Bialgebra.counitAlgHom_apply,
      counit_restrictToBorel_antipode, ite_eq_right_iff.mpr fun h => absurd h.symm hk,
      TensorProduct.tmul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

variable (R n) in
/-- **`𝒪(GL_n)` with left translation, as a comodule over `𝒪(B)`.** -/
@[instance_reducible]
def leftComodule : TauCeti.Comodule R (borelHopf R n) (glHopf R n) where
  coact := (leftCoaction R n).toLinearMap
  coassoc := LinearMap.ext fun x => DFunLike.congr_fun (leftCoaction_coassoc (R := R) (n := n)) x
  lTensor_counit_comp_coact := LinearMap.ext fun x =>
    DFunLike.congr_fun (leftCoaction_counit (R := R) (n := n)) x

/-! ### The coaction on `GLCoord R n` and its points -/

variable (R n) in
/-- `𝒪(GL_n)` (`GLCoord R n`) as a comodule over `𝒪(B)` by left translation: `leftComodule`
transported along Tau Ceti's identification `coordinateHopfAlgebraAlgEquiv`. -/
@[instance_reducible]
def glLeftRegularComodule : TauCeti.Comodule R (borelHopf R n) (GLCoord R n) :=
  letI := leftComodule R n
  transportComodule (C := borelHopf R n) (M := glHopf R n)
    (coordinateHopfAlgebraAlgEquiv R n).symm.toLinearEquiv

variable (R n) in
/-- **The left-translation coaction** `λ : 𝒪(GL_n) → 𝒪(GL_n) ⊗ 𝒪(B)` on `GLCoord R n`,
`(b · f)(g) = f(b⁻¹ g)`. -/
def leftCoactionGL : GLCoord R n →ₐ[R] GLCoord R n ⊗[R] borelHopf R n :=
  (Algebra.TensorProduct.map (coordinateHopfAlgebraAlgEquiv R n).symm.toAlgHom
    (AlgHom.id R (borelHopf R n))).comp
    ((leftCoaction R n).comp (coordinateHopfAlgebraAlgEquiv R n).toAlgHom)

theorem glLeftRegularComodule_coact :
    (glLeftRegularComodule R n).coact = (leftCoactionGL R n).toLinearMap :=
  LinearMap.ext fun _ => rfl

theorem leftCoactionGL_genericMatrix (i j : Fin n) :
    leftCoactionGL R n (FlagVarieties.genericMatrix R n i j) =
      ∑ k, FlagVarieties.genericMatrix R n k j ⊗ₜ[R]
        restrictToBorel R n (HopfAlgebra.antipode R (genericEntry R n i k)) := by
  change Algebra.TensorProduct.map (coordinateHopfAlgebraAlgEquiv R n).symm.toAlgHom
    (AlgHom.id R (borelHopf R n)) (leftCoaction R n (genericEntry R n i j)) = _
  rw [leftCoaction_genericEntry, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem leftCoactionGL_glX (i j : Fin n) :
    leftCoactionGL R n (GLRep.glX i j) =
      ∑ k, GLRep.glX k j ⊗ₜ[R] restrictToBorel R n
          (HopfAlgebra.antipode R (genericEntry R n i k)) := by
  rw [← genericMatrix_eq_glX, leftCoactionGL_genericMatrix]
  simp only [genericMatrix_eq_glX]

/-- The point `g ∈ GL_n(R)` as an algebra map `𝒪(GL_n) → R` (for a field, `GLRep.glPoint g`). -/
def glPoint (g : GL (Fin n) R) : glHopf R n →ₐ[R] R :=
  (GLRep.glEval g).comp (coordinateHopfAlgebraAlgEquiv R n).symm.toAlgHom

theorem glPoint_genericEntry (g : GL (Fin n) R) (i j : Fin n) :
    glPoint g (genericEntry R n i j) = (g : Matrix (Fin n) (Fin n) R) i j := by
  change GLRep.glEval g (FlagVarieties.genericMatrix R n i j) = _
  rw [genericMatrix_eq_glX, GLRep.glEval_glX]

theorem map_glEval_localizedGenericMatrix (g : GL (Fin n) R) :
    (localizedGenericMatrix R n).map (GLRep.glEval g) = (g : Matrix (Fin n) (Fin n) R) := by
  ext a c
  rw [Matrix.map_apply]
  change GLRep.glEval g (FlagVarieties.genericMatrix R n a c) = _
  rw [genericMatrix_eq_glX, GLRep.glEval_glX]

theorem glPoint_antipode_genericEntry (g : GL (Fin n) R) (i k : Fin n) :
    glPoint g (HopfAlgebra.antipode R (genericEntry R n i k)) =
      ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i k := by
  have hinv : ((localizedGenericMatrix R n)⁻¹).map (GLRep.glEval g) =
      ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
    rw [Matrix.coe_units_inv]
    refine (Matrix.inv_eq_right_inv ?_).symm
    rw [← map_glEval_localizedGenericMatrix, ← map_mul_algHom,
      Matrix.mul_nonsing_inv _ (isUnit_det_localizedGenericMatrix R n)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [genericEntry_eq, coordinateHopfAlgebra_antipode_X]
  exact congrFun (congrFun hinv i) k

/-- The point `b ∈ B(R)` as an algebra map `𝒪(B) → R` (for a field, `GLRep.borelPoint b`). -/
def borelPoint (b : GLRep.borel R n) : borelHopf R n →ₐ[R] R :=
  Ideal.Quotient.liftₐ (UpperTriangular.definingHopfIdeal R n).toIdeal
    (glPoint (b : GL (Fin n) R)) fun _ hh =>
      UpperTriangular.definingHopfIdeal_toIdeal_le_ker R n (glPoint (b : GL (Fin n) R))
        (fun i j hji => by rw [← genericEntry_eq, glPoint_genericEntry]; exact b.2 hji) hh

theorem borelPoint_restrictToBorel (b : GLRep.borel R n) (h : glHopf R n) :
    borelPoint b (restrictToBorel R n h) = glPoint (b : GL (Fin n) R) h := by
  change borelPoint b ((UpperTriangular.coordinateMap R n).hom h) = _
  rw [UpperTriangular.coordinateMap_apply]
  rfl

/-- **Contracting `λ` with `b ∈ B(R)` is left translation by `b`**, as an algebra map. -/
theorem rid_map_borelPoint_comp_leftCoactionGL (b : GLRep.borel R n) :
    (Algebra.TensorProduct.rid R R (GLCoord R n)).toAlgHom.comp
        ((Algebra.TensorProduct.map (AlgHom.id R (GLCoord R n)) (borelPoint b)).comp
          (leftCoactionGL R n)) =
      GLRep.leftTranslHom R n b := by
  refine GLRep.algHom_ext_glX fun i j => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, leftCoactionGL_glX, GLRep.leftTranslHom_glX, map_sum,
    map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, borelPoint_restrictToBorel,
      glPoint_antipode_genericEntry]
  rfl

/-- **On points, `λ` is left translation**: contracting with `b ∈ B(R)` gives `leftTranslHom b`. -/
theorem contract_glLeftRegularComodule (b : GLRep.borel R n) :
    GLRep.contract (borelPoint b) (glLeftRegularComodule R n).coact =
      (GLRep.leftTranslHom R n b).toLinearMap := by
  rw [← rid_map_borelPoint_comp_leftCoactionGL, GLRep.contract, glLeftRegularComodule_coact]
  rfl

theorem rid_lTensor_borelPoint_leftCoactionGL (b : GLRep.borel R n) (f : GLCoord R n) :
    TensorProduct.rid R (GLCoord R n)
        ((borelPoint b).toLinearMap.lTensor _ (leftCoactionGL R n f)) =
      GLRep.leftTranslHom R n b f :=
  LinearMap.congr_fun (contract_glLeftRegularComodule b) f

/-! ### Closed subschemes stable under left multiplication by `B` -/

section Quotient

variable (J : Ideal (GLCoord R n))

/-- `λ` followed by the quotient map `𝒪(GL_n) → 𝒪(GL_n)/J`. -/
def leftCoactionMod : GLCoord R n →ₐ[R] (GLCoord R n ⧸ J) ⊗[R] borelHopf R n :=
  (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (AlgHom.id R (borelHopf R n))).comp
    (leftCoactionGL R n)

theorem leftCoactionMod_toLinearMap :
    (leftCoactionMod J).toLinearMap =
      (Ideal.Quotient.mkₐ R J).toLinearMap.rTensor (borelHopf R n) ∘ₗ
        (leftCoactionGL R n).toLinearMap := by
  rw [leftCoactionMod, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
    TensorProduct.AlgebraTensorModule.map_eq, AlgHom.toLinearMap_id]
  rfl

theorem leftCoactionMod_eq (f : GLCoord R n) :
    leftCoactionMod J f =
      (Ideal.Quotient.mkₐ R J).toLinearMap.rTensor (borelHopf R n) (leftCoactionGL R n f) :=
  LinearMap.congr_fun (leftCoactionMod_toLinearMap J) f

/-- **`J` is stable under the left coaction** (comodule sense): `λ(J) ⊆ J ⊗ 𝒪(B)`, i.e. the closed
subscheme `V(J) ⊆ GL_n` is stable under left multiplication by `B`. -/
def IsLeftCoactionStable : Prop :=
  ∀ f ∈ J, leftCoactionGL R n f ∈
    LinearMap.range ((J.restrictScalars R).subtype.rTensor (borelHopf R n))

theorem exact_subtype_mkₐ :
    Function.Exact (J.restrictScalars R).subtype (Ideal.Quotient.mkₐ R J).toLinearMap := fun y => by
  rw [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, fun ⟨z, hz⟩ => hz ▸ z.2⟩

/-- **Criterion**: `λ(J) ⊆ J ⊗ 𝒪(B)` iff `λ(J)` vanishes in `(𝒪(GL_n)/J) ⊗ 𝒪(B)` (right exactness
of `⊗`; no flatness needed). -/
theorem isLeftCoactionStable_iff :
    IsLeftCoactionStable J ↔ J ≤ RingHom.ker (leftCoactionMod J).toRingHom := by
  have hex := _root_.rTensor_exact (borelHopf R n) (exact_subtype_mkₐ J)
    (Ideal.Quotient.mkₐ_surjective R J)
  exact ⟨fun h f hf => RingHom.mem_ker.mpr ((hex _).mpr (h f hf)),
    fun h f hf => (hex _).mp (RingHom.mem_ker.mp (h hf))⟩

/-- **Criterion on generators**: if `J` is generated by elements `f` with `λ(f) ∈ J ⊗ 𝒪(B)`,
then `J` is stable under the left coaction. -/
theorem isLeftCoactionStable_of_span {s : Set (GLCoord R n)} (hJ : J = Ideal.span s)
    (hs : ∀ f ∈ s, leftCoactionMod J f = 0) : IsLeftCoactionStable J :=
  (isLeftCoactionStable_iff J).mpr
    (hJ.le.trans (Ideal.span_le.mpr fun f hf => RingHom.mem_ker.mpr (hs f hf)))

variable {J}

theorem rid_lTensor_borelPoint_leftCoactionMod (b : GLRep.borel R n) (f : GLCoord R n) :
    TensorProduct.rid R (GLCoord R n ⧸ J)
        ((borelPoint b).toLinearMap.lTensor _ (leftCoactionMod J f)) =
      Ideal.Quotient.mk J (GLRep.leftTranslHom R n b f) := by
  change TensorProduct.rid R _ ((borelPoint b).toLinearMap.lTensor _
    ((Ideal.Quotient.mkₐ R J).toLinearMap.rTensor _ (leftCoactionGL R n f))) = _
  rw [rid_lTensor_rTensor_comm, rid_lTensor_borelPoint_leftCoactionGL]
  rfl

/-- Stability under the left coaction implies stability under left translation by `B(R)`. -/
theorem IsLeftCoactionStable.isLeftTranslStable (hJ : IsLeftCoactionStable J) :
    IsLeftTranslStable J := fun b hb f hf => by
  have h0 := RingHom.mem_ker.mp ((isLeftCoactionStable_iff J).mp hJ hf)
  have h1 := rid_lTensor_borelPoint_leftCoactionMod (J := J) ⟨b, hb⟩ f
  rw [show leftCoactionMod J f = 0 from h0, LinearMap.map_zero, LinearEquiv.map_zero] at h1
  exact Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp h1.symm)

/-- The coaction on `𝒪(GL_n)/J`, an algebra map. -/
def leftCoactionQuot (hJ : IsLeftCoactionStable J) :
    (GLCoord R n ⧸ J) →ₐ[R] (GLCoord R n ⧸ J) ⊗[R] borelHopf R n :=
  Ideal.Quotient.liftₐ J (leftCoactionMod J) fun _ hf => (isLeftCoactionStable_iff J).mp hJ hf

theorem leftCoactionQuot_mk (hJ : IsLeftCoactionStable J) (f : GLCoord R n) :
    leftCoactionQuot hJ (Ideal.Quotient.mk J f) = leftCoactionMod J f :=
  rfl

/-- **`𝒪(GL_n)/J` as a comodule over `𝒪(B)`**, for `J` stable under the left coaction. -/
@[instance_reducible]
def quotComodule (hJ : IsLeftCoactionStable J) :
    TauCeti.Comodule R (borelHopf R n) (GLCoord R n ⧸ J) :=
  letI := glLeftRegularComodule R n
  comoduleOfSurjective (Ideal.Quotient.mkₐ R J).toLinearMap (Ideal.Quotient.mkₐ_surjective R J)
    (leftCoactionQuot hJ).toLinearMap fun _ => rfl

theorem quotComodule_coact (hJ : IsLeftCoactionStable J) :
    (quotComodule hJ).coact = (leftCoactionQuot hJ).toLinearMap :=
  rfl

/-- **On points, the coaction on `𝒪(GL_n)/J` is left translation** (`leftTranslQuot`). -/
theorem contract_quotComodule (hJ : IsLeftCoactionStable J) (b : GLRep.borel R n) :
    GLRep.contract (borelPoint b) (quotComodule hJ).coact =
      (leftTranslQuot J hJ.isLeftTranslStable b).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact rid_lTensor_borelPoint_leftCoactionMod b f

end Quotient

/-! ### Over an infinite field: `B(K)`-stable ideals -/

section InfiniteField

variable {K : Type*} [Field K] [Infinite K]

/-- **Points of `B(K)` separate `M ⊗ 𝒪(B)`** over an infinite field, for any `K`-module `M`. -/
theorem tensor_ext_borelPoint {M : Type*} [AddCommGroup M] [Module K M]
    {t t' : M ⊗[K] borelHopf K n}
    (h : ∀ b : GLRep.borel K n, TensorProduct.rid K M ((borelPoint b).toLinearMap.lTensor M t) =
      TensorProduct.rid K M ((borelPoint b).toLinearMap.lTensor M t')) : t = t' :=
  GLRep.tensor_ext_borelPoint h

/-- **Over an infinite field, stability under `B(K)` gives stability under the coaction.** -/
theorem isLeftCoactionStable_of_isLeftTranslStable {J : Ideal (GLCoord K n)}
    (hJ : IsLeftTranslStable J) : IsLeftCoactionStable J := by
  refine (isLeftCoactionStable_iff J).mpr fun f hf =>
    RingHom.mem_ker.mpr (tensor_ext_borelPoint fun b => ?_)
  change TensorProduct.rid K _ ((borelPoint b).toLinearMap.lTensor _ (leftCoactionMod J f)) = _
  rw [rid_lTensor_borelPoint_leftCoactionMod, LinearMap.map_zero, LinearEquiv.map_zero,
    Ideal.Quotient.eq_zero_iff_mem]
  exact hJ b b.2 hf

/-- Over an infinite field the two notions of `B`-stability agree. -/
theorem isLeftCoactionStable_iff_isLeftTranslStable {J : Ideal (GLCoord K n)} :
    IsLeftCoactionStable J ↔ IsLeftTranslStable J :=
  ⟨IsLeftCoactionStable.isLeftTranslStable, isLeftCoactionStable_of_isLeftTranslStable⟩

end InfiniteField

/-! ### Left and right translations commute -/

section Commute

variable (R) in
/-- `(A ⊗ B) ⊗ C ≃ (A ⊗ C) ⊗ B` as algebras: the algebra version of `TensorProduct.rightComm`. -/
def rightCommAlgEquiv (A B C : Type*) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [CommRing C] [Algebra R C] : (A ⊗[R] B) ⊗[R] C ≃ₐ[R] (A ⊗[R] C) ⊗[R] B :=
  (Algebra.TensorProduct.assoc R R R A B C).trans <|
    (Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.TensorProduct.comm R B C)).trans
      (Algebra.TensorProduct.assoc R R R A C B).symm

theorem rightCommAlgEquiv_toLinearEquiv (A B C : Type*) [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] [CommRing C] [Algebra R C] :
    (rightCommAlgEquiv R A B C).toLinearEquiv = TensorProduct.rightComm R A B C :=
  LinearEquiv.toLinearMap_injective (TensorProduct.ext_threefold fun _ _ _ => rfl)

@[simp]
theorem rightCommAlgEquiv_tmul {A B C : Type*} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] [CommRing C] [Algebra R C] (a : A) (b : B) (c : C) :
    rightCommAlgEquiv R A B C ((a ⊗ₜ[R] b) ⊗ₜ[R] c) = (a ⊗ₜ[R] c) ⊗ₜ[R] b :=
  rfl

/-- The entry `π(S x_ik)` of the generic matrix `b⁻¹` of `B`. -/
def borelInverseEntry (i k : Fin n) : borelHopf R n :=
  restrictToBorel R n (HopfAlgebra.antipode R (genericEntry R n i k))

/-- The entry `b_lj` of the generic upper triangular matrix `borelMatrix`. -/
def borelMatrixEntry (l j : Fin n) : BorelCoord R n :=
  borelMatrix R n l j

theorem rightCoaction_glX (i j : Fin n) :
    rightCoaction R n (GLRep.glX i j) = ∑ l, GLRep.glX i l ⊗ₜ[R] borelMatrixEntry (R := R) l j := by
  have h := congrFun (congrFun (map_rightCoaction_genericMatrix R n) i) j
  rw [Matrix.map_apply, Matrix.mul_apply] at h
  rw [← genericMatrix_eq_glX, h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.map_apply, Matrix.map_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    one_mul, genericMatrix_eq_glX]
  rfl

/-- Algebra maps out of `𝒪(GL_n)` (to any `R`-algebra) agreeing on the coordinates are equal. -/
theorem glCoord_algHom_ext_glX {T : Type*} [Semiring T] [Algebra R T] {φ ψ : GLCoord R n →ₐ[R] T}
    (h : ∀ i j, φ (GLRep.glX i j) = ψ (GLRep.glX i j)) : φ = ψ := by
  have h' := coordinateHopfAlgebra_algHom_ext R n
    (f := φ.comp (coordinateHopfAlgebraAlgEquiv R n).symm.toAlgHom)
    (g := ψ.comp (coordinateHopfAlgebraAlgEquiv R n).symm.toAlgHom) fun i j => by
      change φ (FlagVarieties.genericMatrix R n i j) = ψ (FlagVarieties.genericMatrix R n i j)
      rw [genericMatrix_eq_glX]
      exact h i j
  exact AlgHom.ext fun x => DFunLike.congr_fun h' (coordinateHopfAlgebraAlgEquiv R n x)

variable (J : Ideal (GLCoord R n))

theorem rightCoactionMod_glX (i j : Fin n) :
    rightCoactionMod R n J (GLRep.glX i j) =
      ∑ l, Ideal.Quotient.mk J (GLRep.glX i l) ⊗ₜ[R] borelMatrixEntry (R := R) l j := by
  change Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (AlgHom.id R (BorelCoord R n))
    (rightCoaction R n (GLRep.glX i j)) = _
  rw [rightCoaction_glX, map_sum]
  rfl

theorem leftCoactionMod_glX (i j : Fin n) :
    leftCoactionMod J (GLRep.glX i j) =
      ∑ k, Ideal.Quotient.mk J (GLRep.glX k j) ⊗ₜ[R] borelInverseEntry (R := R) i k := by
  change Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R J) (AlgHom.id R (borelHopf R n))
    (leftCoactionGL R n (GLRep.glX i j)) = _
  rw [leftCoactionGL_glX, map_sum]
  rfl

variable {J}

-- The unification of the tensor-product algebra structures over `𝒪(GL_n)/J` is slow.
set_option maxHeartbeats 1000000 in
/-- **Left and right translations commute**, on `𝒪(GL_n)/J`:
`(ρ ⊗ id) ∘ λ = τ ∘ (λ ⊗ id) ∘ ρ`. -/
theorem rightCoactionMod_comm (hJ : IsLeftCoactionStable J) :
    (Algebra.TensorProduct.map (rightCoactionMod R n J) (AlgHom.id R (borelHopf R n))).comp
        (leftCoactionGL R n) =
      (rightCommAlgEquiv R (GLCoord R n ⧸ J) (borelHopf R n)
          (BorelCoord R n)).toAlgHom.comp
        ((Algebra.TensorProduct.map (leftCoactionQuot hJ) (AlgHom.id R (BorelCoord R n))).comp
          (rightCoactionMod R n J)) := by
  refine glCoord_algHom_ext_glX fun i j => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, leftCoactionGL_glX,
    rightCoactionMod_glX, map_sum, map_sum, map_sum]
  have hL : ∀ k, Algebra.TensorProduct.map (rightCoactionMod R n J) (AlgHom.id R (borelHopf R n))
      (GLRep.glX k j ⊗ₜ[R] restrictToBorel R n (HopfAlgebra.antipode R (genericEntry R n i k))) =
      ∑ l, (Ideal.Quotient.mk J (GLRep.glX k l) ⊗ₜ[R] borelMatrixEntry (R := R) l j) ⊗ₜ[R]
          borelInverseEntry (R := R) i k := by
    intro k
    rw [Algebra.TensorProduct.map_tmul, rightCoactionMod_glX, TensorProduct.sum_tmul]
    rfl
  have hR : ∀ l, (rightCommAlgEquiv R (GLCoord R n ⧸ J) (borelHopf R n)
      (BorelCoord R n))
      (Algebra.TensorProduct.map (leftCoactionQuot hJ) (AlgHom.id R (BorelCoord R n))
        (Ideal.Quotient.mk J (GLRep.glX i l) ⊗ₜ[R] borelMatrixEntry (R := R) l j)) =
      ∑ k, (Ideal.Quotient.mk J (GLRep.glX k l) ⊗ₜ[R] borelMatrixEntry (R := R) l j) ⊗ₜ[R]
          borelInverseEntry (R := R) i k := by
    intro l
    have e1 : Algebra.TensorProduct.map (leftCoactionQuot hJ) (AlgHom.id R (BorelCoord R n))
        (Ideal.Quotient.mk J (GLRep.glX i l) ⊗ₜ[R] borelMatrixEntry (R := R) l j) =
        ∑ k, (Ideal.Quotient.mk J (GLRep.glX k l) ⊗ₜ[R] borelInverseEntry (R := R) i k) ⊗ₜ[R]
            borelMatrixEntry (R := R) l j := by
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ← TensorProduct.sum_tmul]
      exact congrArg (· ⊗ₜ[R] borelMatrixEntry (R := R) l j) (leftCoactionMod_glX J i l)
    rw [e1, map_sum]
    rfl
  exact (Finset.sum_congr rfl fun k _ => hL k).trans
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ => (hR l).symm))

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **The coaction commutes with the semi-invariance defect** `D(f) = ρ(f) − f ⊗ η⁻¹`:
`(D ⊗ id)(λ f) = τ((λ ⊗ id)(D f))`. -/
theorem rTensor_semiInvariantDefect_leftCoactionGL (hJ : IsLeftCoactionStable J)
    (η : Fin n → ℤ) (f : GLCoord R n) :
    (semiInvariantDefect R n J η).rTensor (borelHopf R n) (leftCoactionGL R n f) =
      TensorProduct.rightComm R (GLCoord R n ⧸ J) (borelHopf R n) (BorelCoord R n)
        ((leftCoactionQuot hJ).toLinearMap.rTensor (BorelCoord R n)
          (semiInvariantDefect R n J η f)) := by
  set c : BorelCoord R n := (((borelCharacterUnit R n η)⁻¹ : (BorelCoord R n)ˣ) : BorelCoord R n)
  set rc := TensorProduct.rightComm R (GLCoord R n ⧸ J) (borelHopf R n) (BorelCoord R n)
  have hD : ∀ t : GLCoord R n ⊗[R] borelHopf R n, (semiInvariantDefect R n J η).rTensor
      (borelHopf R n) t =
      (rightCoactionMod R n J).toLinearMap.rTensor (borelHopf R n) t -
        rc (((Ideal.Quotient.mkₐ R J).toLinearMap.rTensor (borelHopf R n) t) ⊗ₜ[R] c) := by
    intro t
    induction t with
    | tmul h c' =>
      rw [LinearMap.rTensor_tmul, semiInvariantDefect_apply, TensorProduct.sub_tmul,
        LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.rightComm_tmul]
      rfl
    | add a b ha hb =>
      rw [LinearMap.map_add, ha, hb, LinearMap.map_add, LinearMap.map_add, TensorProduct.add_tmul,
        LinearEquiv.map_add]
      abel
  have hcommL : (rightCoactionMod R n J).toLinearMap.rTensor (borelHopf R n) ∘ₗ
      (leftCoactionGL R n).toLinearMap =
      rc.toLinearMap ∘ₗ (leftCoactionQuot hJ).toLinearMap.rTensor (BorelCoord R n) ∘ₗ
        (rightCoactionMod R n J).toLinearMap := by
    have h := congrArg AlgHom.toLinearMap (rightCoactionMod_comm hJ)
    rw [AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap,
      Algebra.TensorProduct.toLinearMap_map, Algebra.TensorProduct.toLinearMap_map,
      TensorProduct.AlgebraTensorModule.map_eq, TensorProduct.AlgebraTensorModule.map_eq,
      AlgHom.toLinearMap_id, AlgHom.toLinearMap_id, AlgEquiv.toAlgHom_toLinearMap,
      rightCommAlgEquiv_toLinearEquiv] at h
    exact h
  have hc := LinearMap.congr_fun hcommL f
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply, LinearEquiv.coe_coe] at hc
  have hrc : ∀ a b, rc (a - b) = rc a - rc b := fun a b => map_sub rc a b
  rw [hD, hc, semiInvariantDefect_apply,
    map_sub ((leftCoactionQuot hJ).toLinearMap.rTensor (BorelCoord R n)), hrc,
    LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, leftCoactionQuot_mk, leftCoactionMod_eq]

/-- **The coaction preserves the semi-invariants** (`𝒪(B)` is flat over `R`, `instFlatBorelHopf`).
-/
theorem leftCoactionQuot_mem_range (hJ : IsLeftCoactionStable J)
    (η : Fin n → ℤ) {x : GLCoord R n ⧸ J} (hx : x ∈ quotientSemiInvariants R n J η) :
    leftCoactionQuot hJ x ∈
      LinearMap.range ((quotientSemiInvariants R n J η).subtype.rTensor (borelHopf R n)) := by
  obtain ⟨f, hf, rfl⟩ := hx
  have hf' : semiInvariantDefect R n J η f = 0 := hf
  have h0 : (semiInvariantDefect R n J η).rTensor (borelHopf R n) (leftCoactionGL R n f) = 0 := by
    rw [rTensor_semiInvariantDefect_leftCoactionGL hJ, hf', LinearMap.map_zero,
      LinearEquiv.map_zero]
  obtain ⟨t, ht⟩ := (Module.Flat.rTensor_exact (borelHopf R n)
    (LinearMap.exact_subtype_ker_map (semiInvariantDefect R n J η)) (leftCoactionGL R n f)).mp h0
  let φ : LinearMap.ker (semiInvariantDefect R n J η) →ₗ[R] quotientSemiInvariants R n J η :=
    (Ideal.Quotient.mkₐ R J).toLinearMap.restrict fun g hg => ⟨g, hg, rfl⟩
  refine ⟨φ.rTensor (borelHopf R n) t, ?_⟩
  have hφ : (quotientSemiInvariants R n J η).subtype ∘ₗ φ =
      (Ideal.Quotient.mkₐ R J).toLinearMap ∘ₗ
        (LinearMap.ker (semiInvariantDefect R n J η)).subtype :=
    LinearMap.ext fun _ => rfl
  rw [← LinearMap.rTensor_comp_apply, hφ, LinearMap.rTensor_comp_apply, ht]
  exact (leftCoactionMod_eq J f).symm

end Commute

/-! ### The comodule structure on `H⁰(X, 𝓛(η))` -/

section Sections

variable {J : Ideal (GLCoord R n)}

/-- The semi-invariants `(𝒪(GL_n)/J)^{(B, η)}` as a subcomodule of `𝒪(GL_n)/J`. -/
def semiInvSubcomodule (hJ : IsLeftCoactionStable J) (η : Fin n → ℤ) :
    letI := quotComodule hJ
    TauCeti.Subcomodule R (borelHopf R n) (GLCoord R n ⧸ J) :=
  letI := quotComodule hJ
  TauCeti.Subcomodule.ofSubmodule (quotientSemiInvariants R n J η) fun _ hx =>
    leftCoactionQuot_mem_range hJ η hx

/-- The identification of the subcomodule with the submodule of semi-invariants. -/
def semiInvSubcomoduleEquiv (hJ : IsLeftCoactionStable J) (η : Fin n → ℤ) :
    (letI := quotComodule hJ; semiInvSubcomodule hJ η) ≃ₗ[R] quotientSemiInvariants R n J η where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The semi-invariants `(𝒪(GL_n)/J)^{(B, η)}` as a comodule over `𝒪(B)`**, for `J` stable under
the left coaction. -/
@[instance_reducible]
def semiInvariantsComodule (hJ : IsLeftCoactionStable J) (η : Fin n → ℤ) :
    TauCeti.Comodule R (borelHopf R n) (quotientSemiInvariants R n J η) :=
  letI := quotComodule hJ
  transportComodule (C := borelHopf R n) (M := semiInvSubcomodule hJ η)
      (semiInvSubcomoduleEquiv hJ η)

/-- **On points, the coaction on the semi-invariants is left translation**
(`semiInvariantsRep`). -/
theorem contract_semiInvariantsComodule (hJ : IsLeftCoactionStable J) (η : Fin n → ℤ)
    (b : GLRep.borel R n) :
    GLRep.contract (borelPoint b) (semiInvariantsComodule hJ η).coact =
      semiInvariantsRep J hJ.isLeftTranslStable η b := by
  let _ := quotComodule hJ
  refine LinearMap.ext fun x => Subtype.ext ?_
  rw [contract_transportComodule]
  change ((GLRep.contract (borelPoint b) (TauCeti.Comodule.coact (R := R) (C := borelHopf R n)
    (M := semiInvSubcomodule hJ η)) ((semiInvSubcomoduleEquiv hJ η).symm x) :
      semiInvSubcomodule hJ η) : GLCoord R n ⧸ J) = _
  rw [coe_contract_subcomodule', contract_quotComodule]
  rfl

variable (R n) in
/-- **The algebraic-group form of the action of `B` on `H⁰(X, 𝓛(η))`: the `𝒪(B)`-comodule
structure**.

For a closed subscheme `X ⊆ Flₙ` (ideal sheaf `I`) whose preimage ideal `J ⊆ 𝒪(GLₙ)` is stable
under the left coaction (`λ(J) ⊆ J ⊗ 𝒪(B)`, i.e. `π⁻¹X` is stable under left multiplication by
the group scheme `B`), the coaction `λ = (id ⊗ π) ∘ τ ∘ (S ⊗ id) ∘ Δ` of left translation,
`(b · f)(g) = f(b⁻¹ g)`, preserves `(𝒪(GLₙ)/J)^{(B, η)}`; transported through
`sectionsEquivSemiInvariants` it makes `H⁰(X, 𝓛(η))` a comodule over
`𝒪(B)` (Tau Ceti's `UpperTriangular.coordinateHopfAlgebra`). On points it is `sectionsRep`
(`FlagVarieties.contract_sectionsComodule`). It uses that `𝒪(B)` is flat over `R`
(`FlagVarieties.instFlatBorelHopf`). -/
@[instance_reducible]
def sectionsComodule (I : (FlagScheme R n).IdealSheafData) (η : Fin n → ℤ)
    (hJ : IsLeftCoactionStable (preimageIdeal R n I)) :
    TauCeti.Comodule R (UpperTriangular.coordinateHopfAlgebra R n) (sections R n I η) :=
  letI := semiInvariantsComodule hJ η
  transportComodule (C := borelHopf R n) (M := quotientSemiInvariants R n (preimageIdeal R n I) η)
    (sectionsEquivSemiInvariants R n I η).symm

/-- **Compatibility with `sectionsRep`**: contracting the coaction on `H⁰(X, 𝓛(η))` with a point
`b ∈ B(R)` is the left translation `sectionsRep b`. -/
theorem contract_sectionsComodule (I : (FlagScheme R n).IdealSheafData) (η : Fin n → ℤ)
    (hJ : IsLeftCoactionStable (preimageIdeal R n I)) (b : GLRep.borel R n) :
    GLRep.contract (borelPoint b) (sectionsComodule R n I η hJ).coact =
      sectionsRep R n I η hJ.isLeftTranslStable b := by
  let _ := semiInvariantsComodule hJ η
  refine LinearMap.ext fun s => ?_
  rw [contract_transportComodule, LinearEquiv.symm_symm, contract_semiInvariantsComodule]
  rfl

end Sections

/-! ### Over an infinite field: rational representations and comodules -/

section Rational

variable {K : Type*} [Field K]

/-- The functions `b ↦ c(b)` on `B(K)` given by elements `c ∈ 𝒪(B)` are regular on `B`. -/
theorem borelPoint_mem_borelFunctions (c : borelHopf K n) :
    (fun b : GLRep.borel K n => borelPoint b c) ∈ GLRep.borelFunctions K n :=
  GLRep.borelPoint_mem_borelFunctions c

/-- **A finite-dimensional comodule over `𝒪(B)` gives a rational representation of `B(K)`**: if
`ρ(b)` is the contraction of the coaction with `b`, then `ρ` has regular matrix coefficients
(`GLRep.isRationalBorelRep_borelComoduleRep`). -/
theorem isRationalBorelRep_of_contract {M : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (c : TauCeti.Comodule K (borelHopf K n) M)
    (ρ : Representation K (GLRep.borel K n) M)
    (hρ : ∀ b, ρ b = GLRep.contract (borelPoint b) c.coact) : GLRep.IsRationalBorelRep ρ := by
  let _ := c
  have e : ρ = GLRep.borelComoduleRep K n M := MonoidHom.ext fun b => hρ b
  rw [e]
  exact GLRep.isRationalBorelRep_borelComoduleRep

/-- **Over a field, `H⁰(X, 𝓛(η))` is a rational representation of `B`** when finite-dimensional:
its matrix coefficients come from the `𝒪(B)`-comodule structure. -/
theorem isRationalBorelRep_sectionsRep (I : (FlagScheme K n).IdealSheafData) (η : Fin n → ℤ)
    (hJ : IsLeftCoactionStable (preimageIdeal K n I)) [FiniteDimensional K (sections K n I η)] :
    GLRep.IsRationalBorelRep (sectionsRep K n I η hJ.isLeftTranslStable) :=
  isRationalBorelRep_of_contract (sectionsComodule K n I η hJ) _ fun b =>
    (contract_sectionsComodule I η hJ b).symm

variable [Infinite K]

/-- **Over an infinite field, a comodule structure over `𝒪(B)` is determined by its points.** -/
theorem comodule_ext_of_contract {M : Type*} [AddCommGroup M] [Module K M]
    {c₁ c₂ : TauCeti.Comodule K (borelHopf K n) M}
    (h : ∀ b : GLRep.borel K n, GLRep.contract (borelPoint b) c₁.coact = GLRep.contract
        (borelPoint b) c₂.coact) :
    c₁ = c₂ :=
  GLRep.borelComodule_ext h

/-- **Over an infinite field the comodule on `H⁰(X, 𝓛(η))` is the unique one whose point action is
`sectionsRep`.** -/
theorem eq_sectionsComodule_iff (I : (FlagScheme K n).IdealSheafData) (η : Fin n → ℤ)
    (hJ : IsLeftCoactionStable (preimageIdeal K n I))
    (c : TauCeti.Comodule K (borelHopf K n) (sections K n I η)) :
    c = sectionsComodule K n I η hJ ↔
      ∀ b, GLRep.contract (borelPoint b) c.coact = sectionsRep K n I η hJ.isLeftTranslStable b := by
  refine ⟨fun h b => h ▸ contract_sectionsComodule I η hJ b, fun h => ?_⟩
  exact comodule_ext_of_contract fun b => (h b).trans (contract_sectionsComodule I η hJ b).symm

/-- Over an infinite field, every closed subscheme stable under `B(K)` carries the comodule
structure (`IsLeftTranslStable` suffices). -/
abbrev sectionsComoduleOfStable (I : (FlagScheme K n).IdealSheafData) (η : Fin n → ℤ)
    (hJ : IsLeftTranslStable (preimageIdeal K n I)) :
    TauCeti.Comodule K (borelHopf K n) (sections K n I η) :=
  sectionsComodule K n I η (isLeftCoactionStable_of_isLeftTranslStable hJ)

end Rational

end

end FlagVarieties
