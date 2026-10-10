import RSCounterexample.Paper.Quiver.HomSpace
import RSCounterexample.Paper.GL.CharacterMultiplicity
import RSCounterexample.QuiverInvariants.Basic

/-!
# Semi-invariants and multiplicities of one-dimensional characters

For a forward quiver `Q` and integers `σ_p`, one per vertex, the following are equivalent
(`ForwardQuiver.multiplicity_const_pos_iff`):
- the multiplicity of the constant weight `(σ_p, …, σ_p)_p` in the coordinate ring `R_Q` is
  positive;
- some nonzero `f ∈ R_Q` is an eigenfunction of `L = ∏_p GL(d_p)` with the character
  `χ_σ(g) = ∏_p det(g_p)^{σ_p}`: `g · f = χ_σ(g) f`;
- some nonzero polynomial `f` is a semi-invariant of weight `σ` in the sense of
  `QuiverInvariants.FQuiver.IsSemiInvariant`: `f(g · V) = χ_σ(g)⁻¹ f(V)`.

The irreducible module `⊗_p V_p^{(σ_p, …, σ_p)}` is one-dimensional with character `χ_σ`
(`GL.ratLeviIrrep_const_apply`), so by the theorem on `dim Hom_L(V^λ, R_Q)`
(`ForwardQuiver.finrank_intertwiningMap_coordRep_eq_multiplicity_of_gl`, applied to
`glCharacterMultiplicity_holds`) the multiplicity is the dimension of the `χ_σ`-eigenspace. Since
`(g · f)(X) = f(g⁻¹ · X)` (`ForwardQuiver.eval_coordRep`), the eigenfunctions are the
semi-invariants.

## Main definitions

* `ForwardQuiver.toFQuiver`: the underlying quiver, as a `QuiverInvariants.FQuiver`. The
  representations of `Q.toFQuiver` on the vertex family `p ↦ Fin (dim p)` have the coordinates
  `ForwardQuiver.ArrowEntry` of `R_Q`, with the same convention.

## Main results

* `GL.ratLeviIrrep_const_apply`: `V^{(σ_p, …, σ_p)_p}` is the character `χ_σ`.
* `ForwardQuiver.eval_coordRep`: `(g · f)(V) = f(g⁻¹ · V)`.
* `ForwardQuiver.coordRep_eq_smul_iff_isSemiInvariant`.
* `ForwardQuiver.multiplicity_const_pos_iff_exists_eigenfunction`,
  `ForwardQuiver.multiplicity_const_pos_iff`.
-/

open MvPolynomial Schubert.RS.Representation Schubert.RS.HighestWeight

namespace Schubert.RS.GL

noncomputable section

/-! ## The irreducible module of a constant weight -/

theorem polynomialGL_apply_one (n : ℕ) (g : (Square n)ˣ) : polynomialGL n g 1 = 1 :=
  map_one (rowAction g.val)

theorem highestFlag_zero (n : ℕ) : highestFlag (0 : ColumnShape n) = 1 := by
  simp [highestFlag]

/-- The flag-minor model of the empty partition is the trivial representation. -/
theorem flagOrbitRepresentation_apply_of_eq_zero {n : ℕ} {m : ColumnShape n} (hm : m = 0)
    (g : GL (Fin n) ℂ) (x : flagOrbitSpan m) : flagOrbitRepresentation m g x = x := by
  subst hm
  apply Subtype.ext
  rw [flagOrbitRepresentation_val]
  obtain ⟨x, hx⟩ := x
  induction hx using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨h, rfl⟩ := hp
    simp only [highestFlag_zero, polynomialGL_apply_one]
  | zero => exact map_zero _
  | add p q _ _ ip iq => rw [map_add, ip, iq]
  | smul c p _ ip => rw [map_smul, ip]

/-- The partition `λ − λ_last` of a constant weight is empty. -/
theorem polyShape_eq_zero {m : ℕ} (l : TauCeti.DominantWeight m) (hl : ∀ i j, l.1 i = l.1 j) :
    polyShape l = 0 := by
  have hw : shapeWeight (polyShape l) = 0 := by
    rw [shapeWeight_polyShape]
    funext i
    cases m with
    | zero => exact i.elim0
    | succ n => simp [TauCeti.DominantWeight.detShift_succ, hl i (Fin.last n)]
  funext k
  have hk : polyShape l k ≤ shapeWeight (polyShape l) k := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun k' => if k ≤ k' then polyShape l k' else 0) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ k)
    simpa [shapeWeight] using h
  rw [hw] at hk
  simpa using hk

theorem detShift_const {m : ℕ} (c : ℤ) (hm : 0 < m) :
    TauCeti.DominantWeight.detShift (⟨fun _ : Fin m => c, antitone_const⟩ :
      TauCeti.DominantWeight m) = c := by
  cases m with
  | zero => omega
  | succ n => rfl

theorem det_eq_one_of_eq_zero {m : ℕ} (hm : m = 0) (h : GL (Fin m) ℂ) :
    Matrix.GeneralLinearGroup.det h = 1 := by
  subst hm
  ext
  simp [Matrix.det_isEmpty]

variable {s : ℕ} (d : Fin s → ℕ)

/-- The constant dominant weight `(σ_p, …, σ_p)` on every block. -/
def constWeight (σ : Fin s → ℤ) (p : Fin s) : TauCeti.DominantWeight (d p) :=
  ⟨fun _ => σ p, antitone_const⟩

/-- **The irreducible module of a constant weight is one-dimensional**: `L` acts on
`⊗_p V_p^{(σ_p, …, σ_p)}` by the character `χ_σ(g) = ∏_p det(g_p)^{σ_p}`. -/
theorem ratLeviIrrep_const_apply (σ : Fin s → ℤ) (g : LeviGroup d)
    (x : TensorProduct ℂ (PiTensorProduct ℂ fun p =>
      flagOrbitSpan (polyShape (constWeight d σ p))) ℂ) :
    ratLeviIrrep d (constWeight d σ) g x = (leviDetCharacter d σ g : ℂ) • x := by
  have h₁ : leviIrrep d (fun q => polyShape (constWeight d σ q)) g = LinearMap.id := by
    change PiTensorProduct.map (fun q => flagOrbitRepresentation
      (polyShape (constWeight d σ q)) (g q)) = _
    have hq : (fun q => flagOrbitRepresentation (polyShape (constWeight d σ q)) (g q)) =
        fun q => LinearMap.id := by
      funext q
      exact LinearMap.ext (flagOrbitRepresentation_apply_of_eq_zero
        (polyShape_eq_zero _ fun _ _ => rfl) (g q))
    rw [hq, PiTensorProduct.map_id]
  have h₂ : leviDetCharacter d (fun p => (constWeight d σ p).detShift) g =
      leviDetCharacter d σ g := by
    rw [leviDetCharacter_apply, leviDetCharacter_apply]
    refine Finset.prod_congr rfl fun p _ => ?_
    rcases Nat.eq_zero_or_pos (d p) with h | h
    · rw [det_eq_one_of_eq_zero h, one_zpow, one_zpow]
    · rw [constWeight, detShift_const _ h]
  induction x using TensorProduct.inductionOn with
  | tmul w a =>
    rw [ratLeviIrrep, leviTwist, _root_.Representation.tprod_apply, TensorProduct.map_tmul, h₁,
      LinearMap.id_apply, leviDetChar, _root_.Representation.ofLinearCharacter_apply, h₂,
      ← smul_eq_mul, TensorProduct.tmul_smul]
  | add x y hx hy => rw [map_add, hx, hy, smul_add]

/-- A linear functional on `⊗_p V_p^{λ^{(p)}}` that is `1` on the tensor product of the highest
flag polynomials: the product of their values at the identity matrix. -/
def highestFunctional (lam : (p : Fin s) → TauCeti.DominantWeight (d p)) :
    TensorProduct ℂ (PiTensorProduct ℂ fun p => flagOrbitSpan (polyShape (lam p))) ℂ →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin s) ℂ).compLinearMap fun p =>
    (identityEvaluation (d p)).toLinearMap ∘ₗ (flagOrbitSpan (polyShape (lam p))).subtype) ∘ₗ
      (TensorProduct.rid ℂ _).toLinearMap

/-- The tensor product of the highest flag polynomials. -/
def highestVector (lam : (p : Fin s) → TauCeti.DominantWeight (d p)) :
    TensorProduct ℂ (PiTensorProduct ℂ fun p => flagOrbitSpan (polyShape (lam p))) ℂ :=
  PiTensorProduct.tprod ℂ (fun _ => ⟨highestFlag _, highestFlag_mem_orbitSpan _⟩) ⊗ₜ 1

theorem highestFunctional_highestVector (lam : (p : Fin s) → TauCeti.DominantWeight (d p)) :
    highestFunctional d lam (highestVector d lam) = 1 := by
  simp [highestFunctional, highestVector, identityEvaluation_highestFlag]

end

end Schubert.RS.GL

namespace Schubert.RS.Quiver.ForwardQuiver

noncomputable section

open Schubert.RS.GL QuiverInvariants

variable (Q : ForwardQuiver)

/-! ## The underlying quiver -/

/-- **The quiver of `Q`**, without its dimension vector, as a `QuiverInvariants.FQuiver`. Its
arrows, sources and targets are those of `Q`. -/
abbrev toFQuiver : FQuiver where
  s := Q.s
  arrows := Q.arrows
  forward := Q.forward

/-! ## The action on the coordinate ring and semi-invariants -/

/-- The point with coordinates `v ↦ ∑_w M_{wv} x_w`: evaluating a linear substitution by `M` at
`x` is evaluating at this point. -/
def substPoint (M : Matrix Q.ArrowEntry Q.ArrowEntry ℂ) (x : Q.ArrowEntry → ℂ) :
    Q.ArrowEntry → ℂ :=
  fun v => ∑ w, M w v * x w

theorem eval_linearSubst (M : Matrix Q.ArrowEntry Q.ArrowEntry ℂ) (x : Q.ArrowEntry → ℂ)
    (f : Q.coordRing) : eval x (linearSubst M f) = eval (Q.substPoint M x) f := by
  have h : (aeval x).comp (linearSubst M) = aeval (Q.substPoint M x) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [substPoint]
  rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval, ← h]
  rfl

theorem substPoint_coordMatrix (g : LeviGroup Q.dim) (x : Q.ArrowEntry → ℂ) (e : Q.Arrow)
    (i : Fin (Q.dim (Q.src e))) (j : Fin (Q.dim (Q.tgt e))) :
    Q.substPoint (Q.coordMatrix g) x ⟨e, (i, j)⟩ =
      ∑ i', ∑ j', (g (Q.src e) : Matrix _ _ ℂ) i' i *
        (((g (Q.tgt e))⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) j j' * x ⟨e, (i', j')⟩ := by
  have h := congrArg (eval x) (Q.coordRep_X g ⟨e, (i, j)⟩)
  rw [coordRep_apply, eval_linearSubst, eval_X] at h
  rw [h]
  simp only [map_sum, smul_eval, eval_X]

/-- The coordinates of `g⁻¹ · V`, in terms of the matrix of `g` on the linear coordinates. -/
theorem substPoint_coord (g : LeviGroup Q.dim) (V : Q.toFQuiver.Rep ℂ (finFam Q.dim)) :
    Q.substPoint (Q.coordMatrix g) (Q.toFQuiver.coord V) =
      Q.toFQuiver.coord (Q.toFQuiver.act g⁻¹ V) := by
  funext v
  obtain ⟨e, i, j⟩ := v
  refine (Q.substPoint_coordMatrix g _ e i j).trans ?_
  let A : Matrix (Fin (Q.dim (Q.tgt e))) (Fin (Q.dim (Q.tgt e))) ℂ :=
    (((g (Q.tgt e))⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)
  let B : Matrix (Fin (Q.dim (Q.tgt e))) (Fin (Q.dim (Q.src e))) ℂ := V e
  let C : Matrix (Fin (Q.dim (Q.src e))) (Fin (Q.dim (Q.src e))) ℂ := (g (Q.src e) : Matrix _ _ ℂ)
  change ∑ i' : Fin (Q.dim (Q.src e)), ∑ j' : Fin (Q.dim (Q.tgt e)), C i' i * A j j' * B j' i' =
    (A * B * C) j i
  simp only [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **The action on `R_Q` is the contragredient one**: `(g · f)(V) = f(g⁻¹ · V)`. -/
theorem eval_coordRep (g : LeviGroup Q.dim) (f : Q.coordRing)
    (V : Q.toFQuiver.Rep ℂ (finFam Q.dim)) :
    eval (Q.toFQuiver.coord V) (Q.coordRep g f) =
      eval (Q.toFQuiver.coord (Q.toFQuiver.act g⁻¹ V)) f := by
  have h := Q.eval_linearSubst (Q.coordMatrix g) (Q.toFQuiver.coord V) f
  rw [substPoint_coord] at h
  exact h

theorem leviDetCharacter_eq_chi (σ : Fin Q.s → ℤ) (g : LeviGroup Q.dim) :
    leviDetCharacter Q.dim σ g = chi (ι := finFam Q.dim) σ g := by
  rw [leviDetCharacter_apply]
  rfl

/-- **Eigenfunctions of `L` are semi-invariants**: `g · f = χ_σ(g) f` for all `g` if and only if
`f(g · V) = χ_σ(g)⁻¹ f(V)` for all `g` and `V`. -/
theorem coordRep_eq_smul_iff_isSemiInvariant (σ : Fin Q.s → ℤ) (f : Q.coordRing) :
    (∀ g, Q.coordRep g f = (leviDetCharacter Q.dim σ g : ℂ) • f) ↔
      Q.toFQuiver.IsSemiInvariant (ι := finFam Q.dim) σ f := by
  constructor
  · intro h g V
    calc eval (Q.toFQuiver.coord (Q.toFQuiver.act g V)) f
        = eval (Q.toFQuiver.coord V) (Q.coordRep g⁻¹ f) := by rw [Q.eval_coordRep, inv_inv]
      _ = eval (Q.toFQuiver.coord V) ((leviDetCharacter Q.dim σ g⁻¹ : ℂ) • f) := by rw [h]
      _ = (leviDetCharacter Q.dim σ g⁻¹ : ℂ) * eval (Q.toFQuiver.coord V) f := smul_eval _ _ _
      _ = ((chi σ g)⁻¹ : ℂˣ) * eval (Q.toFQuiver.coord V) f := by
        rw [map_inv, leviDetCharacter_eq_chi]
  · intro h g
    apply MvPolynomial.funext
    intro x
    let V := Q.toFQuiver.ofCoord (R := ℂ) (ι := finFam Q.dim) x
    calc eval x (Q.coordRep g f)
        = eval (Q.toFQuiver.coord V) (Q.coordRep g f) := rfl
      _ = eval (Q.toFQuiver.coord (Q.toFQuiver.act g⁻¹ V)) f := Q.eval_coordRep g f V
      _ = ((chi σ g⁻¹)⁻¹ : ℂˣ) * eval (Q.toFQuiver.coord V) f := h g⁻¹ V
      _ = (leviDetCharacter Q.dim σ g : ℂ) * eval x f := by
        rw [← leviDetCharacter_eq_chi, map_inv, inv_inv]
        rfl
      _ = eval x ((leviDetCharacter Q.dim σ g : ℂ) • f) := (smul_eval _ _ _).symm

/-! ## Multiplicities of constant weights -/

/-- **Positive multiplicity of a constant weight is a nonzero eigenfunction**: the multiplicity of
`(σ_p, …, σ_p)_p` in `R_Q` is positive if and only if some nonzero `f ∈ R_Q` satisfies
`g · f = χ_σ(g) f` for all `g ∈ L`. -/
theorem multiplicity_const_pos_iff_exists_eigenfunction (σ : Fin Q.s → ℤ) :
    0 < Q.multiplicity (fun p _ => σ p) ↔
      ∃ f : Q.coordRing, f ≠ 0 ∧ ∀ g, Q.coordRep g f = (leviDetCharacter Q.dim σ g : ℂ) • f := by
  have hm := Q.finrank_intertwiningMap_coordRep_eq_multiplicity_of_gl
    glCharacterMultiplicity_holds (constWeight Q.dim σ)
  have := Q.finiteDimensional_intertwiningMap_coordRep (constWeight Q.dim σ)
  rw [show Q.multiplicity (fun p _ => σ p) = _ from hm.symm, Nat.cast_pos,
    Module.finrank_pos_iff_exists_ne_zero]
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨x, hx⟩ : ∃ x, T x ≠ 0 := by
      by_contra h
      push Not at h
      exact hT (_root_.Representation.IntertwiningMap.ext (LinearMap.ext h))
    refine ⟨T x, hx, fun g => ?_⟩
    rw [← T.isIntertwining, ratLeviIrrep_const_apply, map_smul]
  · rintro ⟨f, hf, hfg⟩
    let T := LinearMap.intertwiningMap_of_isIntertwiningMap
      (ratLeviIrrep Q.dim (constWeight Q.dim σ)) Q.coordRep
      ((highestFunctional Q.dim (constWeight Q.dim σ)).smulRight f) fun g v => by
        rw [LinearMap.smulRight_apply, LinearMap.smulRight_apply, ratLeviIrrep_const_apply,
          map_smul, map_smul, hfg, smul_eq_mul, smul_comm, mul_smul]
    refine ⟨T, fun hT => hf ?_⟩
    have h := congrArg (fun T' : (ratLeviIrrep Q.dim (constWeight Q.dim σ)).IntertwiningMap
      Q.coordRep => T' (highestVector Q.dim (constWeight Q.dim σ))) hT
    simpa [T, highestFunctional_highestVector] using h

/-- **Positive multiplicity of a constant weight is a nonzero semi-invariant**: the multiplicity
of `(σ_p, …, σ_p)_p` in `R_Q` is positive if and only if `Q` has a nonzero semi-invariant of
weight `σ` on the dimension vector of `Q`. -/
theorem multiplicity_const_pos_iff (σ : Fin Q.s → ℤ) :
    0 < Q.multiplicity (fun p _ => σ p) ↔
      ∃ f : MvPolynomial (Q.toFQuiver.Entry (finFam Q.dim)) ℂ, f ≠ 0 ∧
        Q.toFQuiver.IsSemiInvariant σ f := by
  rw [multiplicity_const_pos_iff_exists_eigenfunction]
  exact exists_congr fun f => and_congr_right fun _ =>
    Q.coordRep_eq_smul_iff_isSemiInvariant σ f

end

end Schubert.RS.Quiver.ForwardQuiver
