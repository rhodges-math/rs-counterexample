import RSCounterexample.Paper.GL.Pieces
import RSCounterexample.Paper.Statements.GLCharacterMultiplicity
import Mathlib.LinearAlgebra.PiTensorProduct.Finite

/-!
# Intertwining maps into the coordinate ring of a quiver

For a finite-dimensional representation `σ` of `L = ∏_p GL(V_p)`, intertwining maps `σ → R_Q`
split over the graded pieces of `R_Q`: `Hom_L(σ, R_Q) ≃ ∏_ℓ Hom_L(σ, R_Q[ℓ])` as soon as only
finitely many pieces receive nonzero maps.

For `σ = ⊗_p V_p^{λ^{(p)}}` this is the case. The scalar `z` in block `p` acts on `V^λ` by
`z^{∑_i λ^{(p)}_i}` and on the piece of multidegree `ℓ` by `z^{out_p(ℓ) − in_p(ℓ)}`, so a nonzero
map forces `∑_i λ^{(p)}_i = out_p(ℓ) − in_p(ℓ)` at every vertex. Summing over the vertices up to the
source of an arrow `e` bounds `ℓ_e` by `∑_{p, i} |λ^{(p)}_i|`, as in
`Quiver.ForwardQuiver.multiplicity`.

## Main statements

* `Schubert.RS.Quiver.ForwardQuiver.finrank_intertwiningMap_coordRep_eq_sum`: the splitting.
* `Schubert.RS.GL.ratLeviIrrep_blockScalar`: the central character of `V^λ`.
* `Schubert.RS.Quiver.ForwardQuiver.intertwiningMap_coordPiece_eq_zero`: the central character
  obstruction.
* `Schubert.RS.Quiver.ForwardQuiver.finrank_intertwiningMap_ratLeviIrrep_coordRep`:
  `dim Hom_L(V^λ, R_Q) = ∑_{ℓ ≤ degreeBound λ} dim Hom_L(V^λ, R_Q[ℓ])`.
* `Schubert.RS.Quiver.ForwardQuiver.finrank_intertwiningMap_coordRep_eq_multiplicity`: given the
  character formula for the twisted pieces, `dim Hom_L(V^λ, R_Q) = multiplicity λ`.
-/

namespace Schubert.RS.GL

noncomputable section

open Matrix MvPolynomial Schubert.RS.Representation Schubert.RS.HighestWeight
open scoped TensorProduct

/-! ### Scalars in one block -/

theorem linearSubst_diagonal_const {σ : Type*} [Fintype σ] [DecidableEq σ] (z : ℂ)
    {φ : MvPolynomial σ ℂ} {D : ℕ} (hφ : φ.IsHomogeneous D) :
    Quiver.ForwardQuiver.linearSubst (Matrix.diagonal fun _ => z) φ = z ^ D • φ := by
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Quiver.ForwardQuiver.linearSubst_diagonal_monomial, Finset.prod_pow_eq_pow_sum]
  congr 2
  have h : Finsupp.weight 1 m = D := hφ (mem_support_iff.mp hm)
  rw [← h, Finsupp.weight_eq_sum]
  simp

theorem flagOrbitSpan_le_homogeneous {n : ℕ} (μ : ColumnShape n) :
    flagOrbitSpan μ ≤ homogeneousSubmodule (Fin n × Fin n) ℂ (flagDegree μ) := by
  apply Submodule.span_le.mpr
  rintro p ⟨g, rfl⟩
  exact (mem_homogeneousSubmodule _ _).mpr (rowAction_homogeneous g.val (highestFlag_homogeneous μ))

/-- **The scalar `z` acts on the flag-minor model of `V^μ` by `z^{|μ|}`.** -/
theorem flagOrbitRepresentation_scalar {n : ℕ} (μ : ColumnShape n) (z : ℂˣ)
    (x : flagOrbitSpan μ) :
    flagOrbitRepresentation μ (TauCeti.diagGL fun _ => z) x = ((z : ℂ) ^ flagDegree μ) • x := by
  apply Subtype.ext
  rw [flagOrbitRepresentation_val, Submodule.coe_smul]
  have hrow : rowAction ((TauCeti.diagGL fun _ : Fin n => z : GL (Fin n) ℂ) :
      Matrix (Fin n) (Fin n) ℂ) =
        Quiver.ForwardQuiver.linearSubst (Matrix.diagonal fun _ => (z : ℂ)) := by
    rw [TauCeti.diagGL_coe]
    apply MvPolynomial.algHom_ext
    rintro ⟨r, c⟩
    simp [Matrix.diagonal_apply]
  change rowAction _ x.val = _
  rw [hrow]
  exact linearSubst_diagonal_const _ (flagOrbitSpan_le_homogeneous μ x.2)

variable {s : ℕ} (d : Fin s → ℕ)

/-- The point of the torus that is `z` on the variables of block `p` and `1` elsewhere. -/
def blockScalarTorus (p : Fin s) (z : ℂˣ) : Fin (Quiver.Levi.total d) → ℂˣ :=
  fun k => if (finSigmaFinEquiv.symm k).1 = p then z else 1

theorem blockScalarTorus_pos (p : Fin s) (z : ℂˣ) (q : Fin s) (i : Fin (d q)) :
    blockScalarTorus d p z (Quiver.Levi.pos d q i) = if q = p then z else 1 := by
  simp [blockScalarTorus, Quiver.Levi.pos]

theorem leviTorus_blockScalarTorus_self (p : Fin s) (z : ℂˣ) :
    leviTorus d (blockScalarTorus d p z) p = TauCeti.diagGL fun _ => z := by
  simp only [leviTorus, blockScalarTorus_pos, ite_true]

theorem leviTorus_blockScalarTorus_of_ne {p q : Fin s} (h : q ≠ p) (z : ℂˣ) :
    leviTorus d (blockScalarTorus d p z) q = 1 := by
  simp only [leviTorus, blockScalarTorus_pos, h, ite_false]
  exact map_one TauCeti.diagGL

theorem leviDetCharacter_blockScalar (k : Fin s → ℤ) (p : Fin s) (z : ℂˣ) :
    leviDetCharacter d k (leviTorus d (blockScalarTorus d p z)) = z ^ ((d p : ℤ) * k p) := by
  rw [leviDetCharacter_apply, Finset.prod_eq_single p]
  · rw [leviTorus_blockScalarTorus_self, TauCeti.det_diagGL, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← zpow_natCast, ← zpow_mul]
  · intro q _ hq
    rw [leviTorus_blockScalarTorus_of_ne d hq, map_one, one_zpow]
  · simp

/-- An external tensor product on which one factor acts by a scalar and the others trivially. -/
theorem extTensor_apply_eq_smul {W : Fin s → Type*} [∀ p, AddCommMonoid (W p)]
    [∀ p, Module ℂ (W p)] (ρ : (p : Fin s) → _root_.Representation ℂ (GL (Fin (d p)) ℂ) (W p))
    (g : LeviGroup d) (p : Fin s) (c : ℂ) (hp : ∀ x, ρ p (g p) x = c • x)
    (hq : ∀ q ≠ p, ∀ x, ρ q (g q) x = x) (x : PiTensorProduct ℂ W) :
    extTensor d ρ g x = c • x := by
  have h : extTensor d ρ g = c • LinearMap.id := by
    change PiTensorProduct.map (fun q => ρ q (g q)) = _
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    have hv : (fun q => ρ q (g q) (v q)) = Function.update v p (c • v p) := by
      funext q
      by_cases hqp : q = p
      · subst hqp
        rw [Function.update_self, hp]
      · rw [Function.update_of_ne hqp, hq q hqp]
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, hv,
      MultilinearMap.map_update_smul, Function.update_eq_self, LinearMap.smul_apply,
      LinearMap.id_apply]
  rw [h]
  rfl

/-- **The central character of `V^λ`:** the scalar `z` in block `p` acts by
`z^{∑_i λ^{(p)}_i}`. -/
theorem ratLeviIrrep_blockScalar (lam : (p : Fin s) → TauCeti.DominantWeight (d p)) (p : Fin s)
    (z : ℂˣ)
    (x : TensorProduct ℂ (PiTensorProduct ℂ fun p => flagOrbitSpan (polyShape (lam p))) ℂ) :
    ratLeviIrrep d lam (leviTorus d (blockScalarTorus d p z)) x =
      ((z ^ (∑ i, (lam p).1 i) : ℂˣ) : ℂ) • x := by
  set g := leviTorus d (blockScalarTorus d p z)
  have h1 : ∀ w, leviIrrep d (fun q => polyShape (lam q)) g w =
      ((z : ℂ) ^ flagDegree (polyShape (lam p))) • w :=
    extTensor_apply_eq_smul d _ g p _
      (fun w => by
        change flagOrbitRepresentation _ (leviTorus d (blockScalarTorus d p z) p) w = _
        rw [leviTorus_blockScalarTorus_self]
        exact flagOrbitRepresentation_scalar _ z w)
      (fun q hq w => by
        change flagOrbitRepresentation _ (leviTorus d (blockScalarTorus d p z) q) w = _
        rw [leviTorus_blockScalarTorus_of_ne d hq, map_one]
        rfl)
  have hsum : (flagDegree (polyShape (lam p)) : ℤ) + (d p : ℤ) * (lam p).detShift =
      ∑ i, (lam p).1 i := by
    rw [flagDegree, shapeWeight_polyShape, Nat.cast_sum]
    have h : ∀ i, (((lam p).1 i - (lam p).detShift).toNat : ℤ) = (lam p).1 i - (lam p).detShift :=
      fun i => Int.toNat_of_nonneg (sub_nonneg.mpr ((lam p).detShift_le i))
    simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have h : ratLeviIrrep d lam g = ((z ^ (∑ i, (lam p).1 i) : ℂˣ) : ℂ) • LinearMap.id := by
    apply TensorProduct.ext'
    intro w a
    rw [ratLeviIrrep, leviTwist, _root_.Representation.tprod_apply, TensorProduct.map_tmul, h1,
      leviDetChar, _root_.Representation.ofLinearCharacter_apply, leviDetCharacter_blockScalar,
      LinearMap.smul_apply, LinearMap.id_apply, ← hsum, zpow_add, Units.val_mul, zpow_natCast,
      Units.val_pow_eq_pow_val, ← smul_eq_mul, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul',
      smul_smul, mul_comm]
  rw [h]
  rfl

theorem two_zpow_injective :
    Function.Injective fun k : ℤ => (((Units.mk0 (2 : ℂ) two_ne_zero) ^ k : ℂˣ) : ℂ) := by
  intro a b hab
  have h := congrArg (‖·‖) hab
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, norm_zpow, RCLike.norm_two] at h
  exact zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num) h

end

end Schubert.RS.GL

namespace Schubert.RS.Quiver.ForwardQuiver

noncomputable section

open Matrix MvPolynomial Schubert.RS.GL Schubert.RS.Representation Schubert.RS.HighestWeight

variable (Q : ForwardQuiver)

/-! ### Projections to the graded pieces -/

theorem weightedHomogeneousComponent_coordRep (ℓ : Q.Arrow → ℕ) (g : LeviGroup Q.dim)
    (φ : Q.coordRing) :
    weightedHomogeneousComponent Q.arrowGrading ℓ (Q.coordRep g φ) =
      Q.coordRep g (weightedHomogeneousComponent Q.arrowGrading ℓ φ) := by
  classical
  refine MvPolynomial.induction_on' φ (fun m a => ?_) fun φ ψ hφ hψ => ?_
  · have hm : monomial m a ∈
        weightedHomogeneousSubmodule ℂ Q.arrowGrading (Finsupp.weight Q.arrowGrading m) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    rw [weightedHomogeneousComponent_of_mem hm,
      weightedHomogeneousComponent_of_mem (Q.isWeightedHomogeneous_coordRep g hm)]
    split_ifs <;> simp
  · simp only [map_add, hφ, hψ]

/-- The projection of `R_Q` onto its graded piece of multidegree `ℓ`, an intertwining map. -/
def pieceProj (ℓ : Q.Arrow → ℕ) : Q.coordRep.IntertwiningMap (Q.coordPiece ℓ).toRepresentation where
  toLinearMap := (weightedHomogeneousComponent Q.arrowGrading ℓ).codRestrict
    (Q.coordPiece ℓ).toSubmodule fun φ => weightedHomogeneousComponent_mem _ φ ℓ
  isIntertwining' g := LinearMap.ext fun φ => Subtype.ext
    (Q.weightedHomogeneousComponent_coordRep ℓ g φ)

theorem pieceProj_apply (ℓ : Q.Arrow → ℕ) (φ : Q.coordRing) :
    ((Q.pieceProj ℓ φ : (Q.coordPiece ℓ).toSubmodule) : Q.coordRing) =
      weightedHomogeneousComponent Q.arrowGrading ℓ φ :=
  rfl

/-- The inclusion of a graded piece into `R_Q`. -/
def pieceIncl (ℓ : Q.Arrow → ℕ) : (Q.coordPiece ℓ).toRepresentation.IntertwiningMap Q.coordRep where
  toLinearMap := (Q.coordPiece ℓ).toSubmodule.subtype
  isIntertwining' _ := LinearMap.ext fun _ => rfl

section Decomposition

variable {V : Type*} [AddCommMonoid V] [Module ℂ V]
  (σ : _root_.Representation ℂ (LeviGroup Q.dim) V)

/-- **Intertwining maps into `R_Q` split over the graded pieces**, when only the pieces in `S`
receive nonzero maps. -/
def homDecomposition (S : Finset (Q.Arrow → ℕ))
    (hS : ∀ ℓ ∉ S, ∀ f : σ.IntertwiningMap (Q.coordPiece ℓ).toRepresentation, f = 0) :
    σ.IntertwiningMap Q.coordRep ≃ₗ[ℂ]
      ((ℓ : S) → σ.IntertwiningMap (Q.coordPiece (ℓ : Q.Arrow → ℕ)).toRepresentation) where
  toFun f ℓ := (Q.pieceProj ℓ).comp f
  invFun F := ∑ ℓ : S, (Q.pieceIncl ℓ).comp (F ℓ)
  map_add' f f' := by
    funext ℓ
    ext v
    simp
  map_smul' c f := by
    funext ℓ
    ext v
    simp
  left_inv f := by
    classical
    apply _root_.Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    have h0 : ∀ ℓ ∉ S, weightedHomogeneousComponent Q.arrowGrading ℓ (f v) = 0 := by
      intro ℓ hℓ
      have h := congrArg (fun F : σ.IntertwiningMap (Q.coordPiece ℓ).toRepresentation =>
        ((F v : (Q.coordPiece ℓ).toSubmodule) : Q.coordRing)) (hS ℓ hℓ ((Q.pieceProj ℓ).comp f))
      simpa [pieceProj_apply] using h
    change (∑ ℓ : S, (Q.pieceIncl ℓ).comp ((Q.pieceProj ℓ).comp f)) v = f v
    rw [_root_.Representation.IntertwiningMap.sum_apply]
    calc ∑ ℓ : S, ((Q.pieceIncl ℓ).comp ((Q.pieceProj ℓ).comp f)) v
        = ∑ ℓ ∈ S, weightedHomogeneousComponent Q.arrowGrading ℓ (f v) :=
          Finset.sum_coe_sort S fun ℓ => weightedHomogeneousComponent Q.arrowGrading ℓ (f v)
      _ = ∑ᶠ ℓ, weightedHomogeneousComponent Q.arrowGrading ℓ (f v) :=
          (finsum_eq_sum_of_support_subset _ fun ℓ hℓ => by
            by_contra h
            exact hℓ (h0 ℓ h)).symm
      _ = f v := sum_weightedHomogeneousComponent _ _
  right_inv F := by
    classical
    funext ℓ
    apply _root_.Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change weightedHomogeneousComponent Q.arrowGrading (ℓ : Q.Arrow → ℕ)
      ((∑ ℓ' : S, (Q.pieceIncl ℓ').comp (F ℓ')) v) = ((F ℓ v : _) : Q.coordRing)
    rw [_root_.Representation.IntertwiningMap.sum_apply, map_sum, Finset.sum_eq_single ℓ]
    · exact (weightedHomogeneousComponent_of_mem (F ℓ v).2).trans (ite_eq_left rfl)
    · intro ℓ' _ hℓ'
      exact (weightedHomogeneousComponent_of_mem (F ℓ' v).2).trans
        (ite_eq_right fun h => hℓ' (Subtype.ext h).symm)
    · simp

/-- **`dim Hom_L(σ, R_Q) = ∑_{ℓ ∈ S} dim Hom_L(σ, R_Q[ℓ])`** when only the pieces in `S` receive
nonzero maps. -/
theorem finrank_intertwiningMap_coordRep_eq_sum [Module.Finite ℂ V] (S : Finset (Q.Arrow → ℕ))
    (hS : ∀ ℓ ∉ S, ∀ f : σ.IntertwiningMap (Q.coordPiece ℓ).toRepresentation, f = 0) :
    Module.finrank ℂ (σ.IntertwiningMap Q.coordRep) =
      ∑ ℓ ∈ S, Module.finrank ℂ (σ.IntertwiningMap (Q.coordPiece ℓ).toRepresentation) := by
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := ℂ) (M := V)
  let evP : ∀ ℓ : S, σ.IntertwiningMap (Q.coordPiece ℓ).toRepresentation →ₗ[ℂ]
      (Fin n → (Q.coordPiece ℓ).toSubmodule) := fun ℓ =>
    { toFun := fun f i => f (b i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hevP : ∀ ℓ, Function.Injective (evP ℓ) := by
    intro ℓ f f' h
    apply _root_.Representation.IntertwiningMap.ext
    exact LinearMap.ext_on_range hb fun i => congrFun h i
  have : ∀ ℓ : S, Module.Finite ℂ (σ.IntertwiningMap (Q.coordPiece ℓ).toRepresentation) :=
    fun ℓ => Module.Finite.of_injective (evP ℓ) (hevP ℓ)
  let ev : ∀ ℓ : S, σ.IntertwiningMap (Q.coordPiece ℓ).toRepresentation →ₗ[ℂ]
      (Fin n → Q.coordRing) := fun ℓ =>
    { toFun := fun f i => (f (b i) : Q.coordRing)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ∀ ℓ, Function.Injective (ev ℓ) := by
    intro ℓ f f' h
    apply _root_.Representation.IntertwiningMap.ext
    exact LinearMap.ext_on_range hb fun i => Subtype.ext (congrFun h i)
  rw [(Q.homDecomposition σ S hS).finrank_eq,
    (LinearEquiv.piCongrRight fun ℓ => LinearEquiv.ofInjective (ev ℓ) (hev ℓ)).finrank_eq,
    Module.finrank_pi_fintype ℂ, ← Finset.sum_coe_sort S]
  exact Finset.sum_congr rfl fun ℓ _ => (LinearEquiv.ofInjective (ev ℓ) (hev ℓ)).finrank_eq.symm

end Decomposition

/-! ### The central character obstruction -/

/-- **The scalar `z` in block `p` acts on the graded piece of multidegree `ℓ` by
`z^{out_p(ℓ) − in_p(ℓ)}`.** -/
theorem coordRep_blockScalar {ℓ : Q.Arrow → ℕ} {φ : Q.coordRing}
    (hφ : φ ∈ (Q.coordPiece ℓ).toSubmodule) (p : Fin Q.s) (z : ℂˣ) :
    Q.coordRep (leviTorus Q.dim (blockScalarTorus Q.dim p z)) φ =
      ((z ^ ((Q.outDegree ℓ p : ℤ) - Q.inDegree ℓ p) : ℂˣ) : ℂ) • φ := by
  classical
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmℓ : m ∈ Q.pieceSet ℓ := hφ (mem_support_iff.mp hm)
  rw [coordRep_leviTorus_monomial]
  congr 1
  set x : Fin Q.s → ℂˣ := fun q => if q = p then z else 1
  have hx : ∀ v : Q.ArrowEntry, Q.entryWeight (blockScalarTorus Q.dim p z) v =
      ((x (Q.src v.1) * (x (Q.tgt v.1))⁻¹ : ℂˣ) : ℂ) := by
    intro v
    simp only [entryWeight, blockScalarTorus_pos, Units.val_mul, x]
  simp only [hx, ← Units.val_pow_eq_pow_val, ← Units.coe_prod]
  congr 1
  rw [Finset.prod_congr rfl fun v _ => mul_pow _ _ _, Finset.prod_mul_distrib,
    Q.prod_pow_src hmℓ x, Q.prod_pow_tgt hmℓ fun q => (x q)⁻¹,
    Finset.prod_eq_single p (fun q _ hq => by simp [x, hq]) (by simp),
    Finset.prod_eq_single p (fun q _ hq => by simp [x, hq]) (by simp)]
  simp [x, zpow_sub, inv_pow]

/-- **The central character obstruction:** `Hom_L(V^λ, R_Q[ℓ]) = 0` unless
`∑_i λ^{(p)}_i = out_p(ℓ) − in_p(ℓ)` at every vertex `p`. -/
theorem intertwiningMap_coordPiece_eq_zero (lam : (p : Fin Q.s) → TauCeti.DominantWeight (Q.dim p))
    {ℓ : Q.Arrow → ℕ} {p : Fin Q.s}
    (h : ∑ i, (lam p).1 i ≠ (Q.outDegree ℓ p : ℤ) - Q.inDegree ℓ p)
    (f : (ratLeviIrrep Q.dim lam).IntertwiningMap (Q.coordPiece ℓ).toRepresentation) : f = 0 := by
  set z : ℂˣ := Units.mk0 (2 : ℂ) two_ne_zero
  set g := leviTorus Q.dim (blockScalarTorus Q.dim p z)
  have hne : ((z ^ (∑ i, (lam p).1 i) : ℂˣ) : ℂ) ≠
      ((z ^ ((Q.outDegree ℓ p : ℤ) - Q.inDegree ℓ p) : ℂˣ) : ℂ) :=
    fun heq => h (two_zpow_injective heq)
  apply _root_.Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have h1 := _root_.Representation.IntertwiningMap.isIntertwining _ _ f g x
  rw [ratLeviIrrep_blockScalar, map_smul] at h1
  have h2 := Q.coordRep_blockScalar (f x).2 p z
  have h3 : (((z ^ (∑ i, (lam p).1 i) : ℂˣ) : ℂ) -
      ((z ^ ((Q.outDegree ℓ p : ℤ) - Q.inDegree ℓ p) : ℂˣ) : ℂ)) •
        ((f x : (Q.coordPiece ℓ).toSubmodule) : Q.coordRing) = 0 := by
    rw [sub_smul, sub_eq_zero]
    have h4 := congrArg Subtype.val h1
    rw [Submodule.coe_smul] at h4
    rw [h4]
    exact h2
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact absurd (sub_eq_zero.mp h4) hne
  · exact Subtype.ext h4

/-- **The cut bound:** if `∑_i λ^{(p)}_i = out_p(ℓ) − in_p(ℓ)` at every vertex, then every `ℓ_e` is
at most `degreeBound λ`. -/
theorem le_degreeBound {lam : Q.Weight} {ℓ : Q.Arrow → ℕ}
    (h : ∀ p, ∑ i, lam p i = (Q.outDegree ℓ p : ℤ) - Q.inDegree ℓ p) (e : Q.Arrow) :
    ℓ e ≤ Q.degreeBound lam := by
  classical
  set F := Finset.univ.filter fun p : Fin Q.s => p ≤ Q.src e
  have hout : ∀ p, (Q.outDegree ℓ p : ℤ) = ∑ a, if Q.src a = p then (ℓ a : ℤ) else 0 := by
    intro p
    rw [outDegree, Nat.cast_sum, Finset.sum_filter]
  have hin : ∀ p, (Q.inDegree ℓ p : ℤ) = ∑ a, if Q.tgt a = p then (ℓ a : ℤ) else 0 := by
    intro p
    rw [inDegree, Nat.cast_sum, Finset.sum_filter]
  have hcut : ∑ p ∈ F, ((Q.outDegree ℓ p : ℤ) - Q.inDegree ℓ p) =
      ∑ a, ((if Q.src a ∈ F then (ℓ a : ℤ) else 0) - (if Q.tgt a ∈ F then (ℓ a : ℤ) else 0)) := by
    simp only [hout, hin, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (s := F), Finset.sum_comm (s := F)]
    simp only [Finset.sum_ite_eq]
  have hnonneg : ∀ a ∈ Finset.univ,
      0 ≤ (if Q.src a ∈ F then (ℓ a : ℤ) else 0) - (if Q.tgt a ∈ F then (ℓ a : ℤ) else 0) := by
    intro a _
    by_cases ht : Q.tgt a ∈ F
    · have hs : Q.src a ∈ F := by
        simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        exact (Q.src_lt_tgt a).le.trans ht
      simp [hs, ht]
    · simp only [ht, ite_false, sub_zero]
      split_ifs <;> simp
  have he : (if Q.src e ∈ F then (ℓ e : ℤ) else 0) - (if Q.tgt e ∈ F then (ℓ e : ℤ) else 0) =
      ℓ e := by
    have hs : Q.src e ∈ F := by simp [F]
    have ht : Q.tgt e ∉ F := by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
      exact Q.src_lt_tgt e
    simp [hs, ht]
  have hle : (ℓ e : ℤ) ≤ ∑ p ∈ F, ((Q.outDegree ℓ p : ℤ) - Q.inDegree ℓ p) := by
    rw [hcut, ← he]
    exact Finset.single_le_sum hnonneg (Finset.mem_univ e)
  have hbound : ∑ p ∈ F, ((Q.outDegree ℓ p : ℤ) - Q.inDegree ℓ p) ≤ (Q.degreeBound lam : ℤ) := by
    calc ∑ p ∈ F, ((Q.outDegree ℓ p : ℤ) - Q.inDegree ℓ p) = ∑ p ∈ F, ∑ i, lam p i :=
          Finset.sum_congr rfl fun p _ => (h p).symm
      _ ≤ ∑ p ∈ F, ∑ i, |lam p i| :=
          Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun i _ => le_abs_self _
      _ ≤ ∑ p, ∑ i, |lam p i| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ =>
            Finset.sum_nonneg fun i _ => abs_nonneg _
      _ = (Q.degreeBound lam : ℤ) := by
          simp [degreeBound]
  exact_mod_cast hle.trans hbound

/-- **Only the pieces of multidegree at most `degreeBound λ` receive maps from `V^λ`:**
`dim Hom_L(V^λ, R_Q) = ∑_{ℓ ≤ degreeBound λ} dim Hom_L(V^λ, R_Q[ℓ])`. -/
theorem finrank_intertwiningMap_ratLeviIrrep_coordRep
    (lam : (p : Fin Q.s) → TauCeti.DominantWeight (Q.dim p)) :
    Module.finrank ℂ ((ratLeviIrrep Q.dim lam).IntertwiningMap Q.coordRep) =
      ∑ ℓ ∈ Fintype.piFinset fun _ : Q.Arrow =>
          Finset.range (Q.degreeBound (fun p => (lam p).1) + 1),
        Module.finrank ℂ ((ratLeviIrrep Q.dim lam).IntertwiningMap
          (Q.coordPiece ℓ).toRepresentation) := by
  refine Q.finrank_intertwiningMap_coordRep_eq_sum (ratLeviIrrep Q.dim lam) _ fun ℓ hℓ f => ?_
  rw [Fintype.mem_piFinset] at hℓ
  push Not at hℓ
  obtain ⟨e, he⟩ := hℓ
  by_contra hf
  have hcut : ∀ p, ∑ i, (lam p).1 i = (Q.outDegree ℓ p : ℤ) - Q.inDegree ℓ p := by
    intro p
    by_contra hp
    exact hf (Q.intertwiningMap_coordPiece_eq_zero lam hp f)
  have := Q.le_degreeBound (lam := fun p => (lam p).1) hcut e
  simp only [Finset.mem_range, not_lt] at he
  omega

/-! ### The multiplicity -/

/-- **`dim Hom_L(V^λ, R_Q)` is the quiver multiplicity**, given the character formula for the
twisted graded pieces: for every multidegree `ℓ` and every `c` with `c_q ≥ in_q(ℓ)` and
`λ + c` polynomial, `dim Hom_L(V^{λ + c}, R_Q[ℓ] ⊗ det^c)` is the coefficient of
`∏_p s_{λ^{(p)} + c_p}` in its character. -/
theorem finrank_intertwiningMap_coordRep_eq_multiplicity
    (lam : (p : Fin Q.s) → TauCeti.DominantWeight (Q.dim p))
    (H : ∀ (ℓ : Q.Arrow → ℕ) (c : Fin Q.s → ℕ), (∀ q, Q.inDegree ℓ q ≤ c q) →
      (∀ p, ((lam p).shift (c p)).IsPolynomial) →
      (Module.finrank ℂ ((ratLeviIrrep Q.dim fun p => (lam p).shift (c p)).IntertwiningMap
          (Q.twistedPiece ℓ c)) : ℤ) =
        Levi.schurCoeff Q.dim (toLaurent (Q.twistedPieceCharacter ℓ c))
          fun p => ((lam p).shift (c p)).1) :
    (Module.finrank ℂ ((ratLeviIrrep Q.dim lam).IntertwiningMap Q.coordRep) : ℤ) =
      Q.multiplicity fun p => (lam p).1 := by
  rw [finrank_intertwiningMap_ratLeviIrrep_coordRep, Nat.cast_sum, multiplicity]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  set c : Fin Q.s → ℕ := fun q => Q.inDegree ℓ q + (-(lam q).detShift).toNat
  have hc : ∀ q, Q.inDegree ℓ q ≤ c q := fun q => Nat.le_add_right _ _
  have hpoly : ∀ p, ((lam p).shift (c p)).IsPolynomial := by
    intro p i
    rw [TauCeti.DominantWeight.shift_apply]
    have h1 := (lam p).detShift_le i
    have h2 := Int.self_le_toNat (-(lam p).detShift)
    simp only [c]
    push_cast
    omega
  rw [finrank_intertwiningMap_ratLeviIrrep_shift Q.dim lam _ fun q => (c q : ℤ)]
  rw [H ℓ c hc hpoly, Q.toLaurent_twistedPieceCharacter ℓ c hc]
  have hw : (fun p => ((lam p).shift (c p)).1) = fun p i => (lam p).1 i + (c p : ℤ) := by
    funext p i
    simp
  rw [hw, schurCoeff_mul_blockDetMonomial]
  rfl

/-- **`dim Hom_L(V^λ, R_Q) = multiplicity λ`**, given `GLCharacterMultiplicity` (for polynomial
representations, `dim Hom_L(V^μ, W)` is the coefficient of `∏_p s_{μ^{(p)}}` in the character of
`W`), applied to `L = ∏_p GL(dim p)` and the twisted graded pieces of `R_Q`. -/
theorem finrank_intertwiningMap_coordRep_eq_multiplicity_of (hgl : GLCharacterMultiplicity)
    (lam : (p : Fin Q.s) → TauCeti.DominantWeight (Q.dim p)) :
    (Module.finrank ℂ ((ratLeviIrrep Q.dim lam).IntertwiningMap Q.coordRep) : ℤ) =
      Q.multiplicity fun p => (lam p).1 :=
  Q.finrank_intertwiningMap_coordRep_eq_multiplicity lam fun ℓ c hc hpoly =>
    hgl Q.s Q.dim (TensorProduct ℂ (Q.coordPiece ℓ).toSubmodule ℂ) (Q.twistedPiece ℓ c)
      (Q.twistedPieceCharacter ℓ c) (Q.isPolynomialLeviRep_twist_coordPiece ℓ c hc)
      (Q.isLeviCharacter_twist_coordPiece ℓ c hc) _ hpoly

end

end Schubert.RS.Quiver.ForwardQuiver
