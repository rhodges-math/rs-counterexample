import Schubert.RS.Quiver.OfTriple
import Schubert.RS.Quiver.CompleteWindow
import Schubert.RS.Window.General
import Schubert.RS.Family.LaurentRelabel
import Schubert.RS.WeylRootSeries

/-!
# Atom coefficients of quiver triples are quiver multiplicities

Theorem 5.3 of the paper at the level of characters: for a quiver partition `I` of `(a, b, c)`,

`[𝒜_c](κ_a κ_b) = m_Q(λ)`,

the multiplicity of `⊗_p V_p^{λ^{(p)}}` in the coordinate ring of the representation space of the
quiver `Q = quiverOf a b c N I`, summed over graded pieces.

The proof follows (5.5) and (5.6) of the paper. Proposition 2.13
(`Window.window_rational_extraction`) writes the atom coefficient as the coefficient of `x^{c−a−b}`
in `∏_{i<j} (1 − x_i/x_j)^{−cmp((a_i,b_i,c̄_i),(a_j,b_j,c̄_j))}`. For a quiver partition the
exponent is `−1` inside an interval and the number of arrows `p → q` between intervals `p < q`, so
the product is the product of the vertex Weyl factors `∏_p Δ(x_{I_p})` and, for every arrow `p → q`,
of the geometric series `∏_{i ∈ I_p, j ∈ I_q} (1 − x_i/x_j)^{−1} = ∑_ℓ h_ℓ(x_i/x_j)`. In the
coefficient window of `x^{c−a−b}` only the terms with `ℓ` at most the degree bound matter
(`sum_hsymm_window`), and what remains is the Levi Weyl projector of the characters of the graded
pieces, relabelled from the quiver's variables to the positions `0, …, n − 1`.

## Main results

* `Schubert.RS.Quiver.rootProduct_eq`: the regrouping of the root factors into vertex Weyl factors
  and arrow series.
* `Schubert.RS.Quiver.atomCoefficient_eq_multiplicity`: Theorem 5.3 at the level of characters.
-/

namespace Schubert.RS.Quiver

noncomputable section

open MvPolynomial Representation

variable {n : ℕ}

/-! ## Positions of the vertex variables -/

namespace IntervalPartition

variable (I : IntervalPartition n)

/-- The relabelling `Fin (∑_p |I_p|) ≃ Fin n` of the variables of the quiver: variable `k` of
vertex `p` sits at position `I.embedding p k`. -/
def blockEquiv : Fin (Levi.total I.blocksFun) ≃ Fin n :=
  finSigmaFinEquiv.symm.trans I.blocksFinEquiv

@[simp] theorem blockEquiv_pos (p : Fin I.length) (k : Fin (I.blocksFun p)) :
    I.blockEquiv (Levi.pos I.blocksFun p k) = I.embedding p k := by
  simp only [blockEquiv, Levi.pos, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

theorem blockEquiv_apply (k : Fin (Levi.total I.blocksFun)) :
    I.blockEquiv k = I.embedding (finSigmaFinEquiv.symm k).1 (finSigmaFinEquiv.symm k).2 :=
  rfl

/-- The last position of block `p`. -/
def last (p : Fin I.length) : Fin n :=
  I.embedding p ⟨I.blocksFun p - 1, Nat.sub_lt (I.one_le_blocksFun p) Nat.one_pos⟩

theorem embedding_le_last (p : Fin I.length) (k : Fin (I.blocksFun p)) :
    I.embedding p k ≤ I.last p :=
  (I.embedding p).monotone (Fin.le_def.mpr (Nat.le_sub_one_of_lt k.isLt))

/-- For blocks `p < q`, the simple-root coordinate at the last position of block `p`. Every root
`x_i/x_j` with `i ∈ I_p` and `j ∈ I_q` contains it exactly once (`rootDegree_crossCut`). -/
def crossCut {p q : Fin I.length} (hpq : p < q) : Fin (n - 1) :=
  rootFirstCut (I.last p) (I.embedding q ⟨0, I.one_le_blocksFun q⟩)
    (I.embedding_lt_embedding hpq _ _)

theorem rootDegree_crossCut {p q : Fin I.length} (hpq : p < q) (k : Fin (I.blocksFun p))
    (l : Fin (I.blocksFun q)) :
    rootDegree (I.embedding p k) (I.embedding q l) (I.crossCut hpq) = 1 := by
  have h1 : (I.embedding p k).val ≤ (I.last p).val := I.embedding_le_last p k
  have h2 : (I.last p).val < (I.embedding q l).val := I.embedding_lt_embedding hpq _ l
  rw [rootDegree_apply]
  simp only [crossCut, rootFirstCut, Fin.val_mk, h1, h2, and_self, ↓reduceIte]

end IntervalPartition

/-! ## Arrows of a forward quiver -/

/-- A product over the arrows of a quantity depending only on the source and the target. -/
theorem ForwardQuiver.prod_arrow {M : Type*} [CommMonoid M] (Q : ForwardQuiver)
    (f : Fin Q.s → Fin Q.s → M) :
    ∏ e : Q.Arrow, f (Q.src e) (Q.tgt e) = ∏ p, ∏ q, f p q ^ Q.arrows p q := by
  rw [Fintype.prod_sigma, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun p _ => Finset.prod_congr rfl fun q _ => ?_
  simp [ForwardQuiver.src, ForwardQuiver.tgt, Finset.prod_const]

/-! ## The factors in simple-root coordinates -/

section Factors

variable (I : IntervalPartition n)

/-- The vertex Weyl factor `Δ(x_{I_p}) = ∏_{i<j ∈ I_p} (1 − x_i/x_j)` in simple-root coordinates,
as a power series. -/
def vertexWeylSeries (p : Fin I.length) : MvPowerSeries (Fin (n - 1)) ℤ :=
  ∏ k : Fin (I.blocksFun p), ∏ l ∈ Finset.univ.filter (k < ·),
    (1 - MvPowerSeries.monomial (rootDegree (I.embedding p k) (I.embedding p l)) 1)

/-- The product of the vertex Weyl factors `∏_p Δ(x_{I_p})` in simple-root coordinates. -/
def weylPoly : MvPolynomial (Fin (n - 1)) ℤ :=
  ∏ p, ∏ k : Fin (I.blocksFun p), ∏ l ∈ Finset.univ.filter (k < ·),
    (1 - monomial (rootDegree (I.embedding p k) (I.embedding p l)) 1)

theorem coe_weylPoly :
    (weylPoly I : MvPowerSeries (Fin (n - 1)) ℤ) = ∏ p, vertexWeylSeries I p := by
  change MvPolynomial.coeToMvPowerSeries.ringHom (weylPoly I) = _
  simp only [weylPoly, vertexWeylSeries, map_prod, map_sub, map_one,
    MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial]

/-- `∏_{i ∈ I_p, j ∈ I_q} (1 − x_i/x_j)^{−1}` in simple-root coordinates. -/
def arrowSeries (p q : Fin I.length) : MvPowerSeries (Fin (n - 1)) ℤ :=
  ∏ kl : Fin (I.blocksFun p) × Fin (I.blocksFun q),
    rootGeometricSeries (rootDegree (I.embedding p kl.1) (I.embedding q kl.2))

/-- `∑_{m ≤ B} h_m(x_i/x_j : i ∈ I_p, j ∈ I_q)` in simple-root coordinates: the characters of the
graded pieces of degree at most `B` of `Sym(V_p ⊗ V_q^*)`. -/
def arrowPoly (B : ℕ) (p q : Fin I.length) : MvPolynomial (Fin (n - 1)) ℤ :=
  ∑ m ∈ Finset.range (B + 1),
    aeval (fun kl : Fin (I.blocksFun p) × Fin (I.blocksFun q) =>
      (monomial (rootDegree (I.embedding p kl.1) (I.embedding q kl.2)) 1 :
        MvPolynomial (Fin (n - 1)) ℤ))
      (hsymm (Fin (I.blocksFun p) × Fin (I.blocksFun q)) ℤ m)

theorem arrowPoly_window (B : ℕ) {p q : Fin I.length} (hpq : p < q) (β : RootDegree n)
    (hB : ∀ i, β i ≤ B) :
    WindowEq β (arrowPoly I B p q : MvPowerSeries (Fin (n - 1)) ℤ) (arrowSeries I p q) := by
  have hw := sum_hsymm_window
    (fun kl : Fin (I.blocksFun p) × Fin (I.blocksFun q) =>
      rootDegree (I.embedding p kl.1) (I.embedding q kl.2))
    (I.crossCut hpq) (fun kl => I.rootDegree_crossCut hpq kl.1 kl.2) β B (hB _)
  exact hw

end Factors

/-! ## Regrouping the root factors -/

section Regroup

variable {a b c : Composition n} {N : ℕ} {I : IntervalPartition n}

/-- A double product over positions, split into blocks. -/
theorem prod_prod_embedding {M : Type*} [CommMonoid M] (I : IntervalPartition n)
    (g : Fin n → Fin n → M) :
    ∏ i, ∏ j, g i j =
      ∏ p, ∏ k : Fin (I.blocksFun p), ∏ q, ∏ l : Fin (I.blocksFun q),
        g (I.embedding p k) (I.embedding q l) :=
  calc ∏ i, ∏ j, g i j = ∏ p, ∏ k : Fin (I.blocksFun p), ∏ j, g (I.embedding p k) j :=
        (_root_.Composition.prod_prod_apply_embedding (fun i => ∏ j, g i j) I).symm
    _ = _ := Finset.prod_congr rfl fun p _ => Finset.prod_congr rfl fun k _ =>
        (_root_.Composition.prod_prod_apply_embedding (fun j => g (I.embedding p k) j) I).symm

theorem cmpFactor_natCast {σ : Type*} (m : ℕ) (d : σ →₀ ℕ) :
    Window.cmpFactor (m : ℤ) d = rootGeometricSeries d ^ m := by
  simp [Window.cmpFactor]

theorem cmpFactor_neg_one {σ : Type*} (d : σ →₀ ℕ) :
    Window.cmpFactor (-1) d = 1 - MvPowerSeries.monomial d 1 := by
  simp [Window.cmpFactor]

/-- The root factors between two blocks: the vertex Weyl factor for a block with itself, and the
`k_{pq}`-th power of the arrow series for blocks `p < q`. -/
theorem prod_block_pair (h : IsQuiverPartition a b c N I) (p q : Fin I.length) :
    ∏ k : Fin (I.blocksFun p), ∏ l : Fin (I.blocksFun q),
      (if I.embedding p k < I.embedding q l then
        Window.cmpFactor
          (Window.cmp (Window.triple a b (Window.complement N c) (I.embedding p k))
            (Window.triple a b (Window.complement N c) (I.embedding q l)))
          (rootDegree (I.embedding p k) (I.embedding q l)) else 1) =
      (if p = q then vertexWeylSeries I p else 1) *
        arrowSeries I p q ^ (quiverOf a b c N I).arrows p q := by
  rcases lt_trichotomy p q with hpq | rfl | hpq
  · have hlt : ∀ k l, I.embedding p k < I.embedding q l := I.embedding_lt_embedding hpq
    simp only [hlt, ↓reduceIte, hpq.ne, one_mul, h.cmp_eq_arrows hpq, cmpFactor_natCast,
      arrowSeries, Fintype.prod_prod_type, Finset.prod_pow]
  · have h0 : (quiverOf a b c N I).arrows p p = 0 := by
      simp
    rw [h0, pow_zero, mul_one]
    split_ifs with hpp
    swap
    · exact absurd rfl hpp
    rw [vertexWeylSeries]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun l _ => ?_
    by_cases hkl : k < l
    · have hlt : I.embedding p k < I.embedding p l := (I.embedding p).lt_iff_lt.mpr hkl
      rw [h.cmp_eq_neg_one hlt ((I.index_embedding p k).trans (I.index_embedding p l).symm)]
      simp [hlt, hkl, cmpFactor_neg_one]
    · have hlt : ¬ I.embedding p k < I.embedding p l := fun h' =>
        hkl ((I.embedding p).lt_iff_lt.mp h')
      simp [hlt, hkl]
  · have hnlt : ∀ k l, ¬ I.embedding p k < I.embedding q l := fun k l =>
      not_lt.mpr (I.embedding_lt_embedding hpq l k).le
    have h0 : (quiverOf a b c N I).arrows p q = 0 := by
      simp [not_lt.mpr hpq.le]
    rw [h0, pow_zero, mul_one]
    simp [hnlt, hpq.ne']

/-- **The root factors of a quiver partition** (the step to (5.5) in the paper): the product
`∏_{i<j} (1 − x_i/x_j)^{−cmp}` is the product of the vertex Weyl factors and, for every arrow
`p → q`, of the series `∏_{i ∈ I_p, j ∈ I_q} (1 − x_i/x_j)^{−1}`. -/
theorem rootProduct_eq (h : IsQuiverPartition a b c N I) :
    ∏ r : PositiveRoot n,
      Window.cmpFactor
        (Window.cmp (Window.triple a b (Window.complement N c) r.val.1)
          (Window.triple a b (Window.complement N c) r.val.2))
        (rootDegree r.val.1 r.val.2) =
      (weylPoly I : MvPowerSeries (Fin (n - 1)) ℤ) *
        ∏ e : (quiverOf a b c N I).Arrow,
          arrowSeries I ((quiverOf a b c N I).src e) ((quiverOf a b c N I).tgt e) := by
  rw [ForwardQuiver.prod_arrow (quiverOf a b c N I) (arrowSeries I), coe_weylPoly]
  refine (positiveRoot_product (fun i j => Window.cmpFactor
    (Window.cmp (Window.triple a b (Window.complement N c) i)
      (Window.triple a b (Window.complement N c) j)) (rootDegree i j))).symm.trans ?_
  simp only [Finset.prod_filter]
  rw [prod_prod_embedding I, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Finset.prod_comm]
  have hW : vertexWeylSeries I p = ∏ q, (if p = q then vertexWeylSeries I p else 1) := by
    rw [Finset.prod_ite_eq]
    simp
  rw [hW, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun q _ => prod_block_pair h p q

end Regroup

/-! ## Relabelling the quiver variables -/

section Relabel

theorem weightRelabel_positiveRoot {m : ℕ} (e : Fin m ≃ Fin n) (x y : Fin m) :
    Family.weightRelabel e (positiveRoot x y) = positiveRoot (e x) (e y) := by
  simp [positiveRoot, map_sub]

theorem laurentRelabel_positiveRoot {m : ℕ} (e : Fin m ≃ Fin n) (x y : Fin m) :
    Family.laurentRelabel e (AddMonoidAlgebra.single (positiveRoot x y) 1) =
      AddMonoidAlgebra.single (positiveRoot (e x) (e y)) 1 := by
  rw [Family.laurentRelabel_single, weightRelabel_positiveRoot]

theorem rootCoordinateEmbedding_monomial_rootDegree {i j : Fin n} (hij : i < j) :
    rootCoordinateEmbedding (monomial (rootDegree i j) (1 : ℤ)) =
      AddMonoidAlgebra.single (positiveRoot i j) 1 := by
  rw [rootCoordinateEmbedding_monomial, rootWeight_rootDegree i j hij]

theorem coeff_rootCoordinateEmbedding (P : MvPolynomial (Fin (n - 1)) ℤ) (d : RootDegree n) :
    (rootCoordinateEmbedding P).coeff (rootWeight d) = P.coeff d := by
  change Finsupp.mapDomain rootWeight (AddMonoidAlgebra.coeff P) (rootWeight d) = _
  exact Finsupp.mapDomain_apply_of_injective rootWeight_injective _ _

/-- A ring homomorphism commutes with substitution into integer polynomials. -/
theorem map_aeval_int {F σ A B : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]
    [FunLike F A B] [RingHomClass F A B] (φ : F) (g : σ → A) (P : MvPolynomial σ ℤ) :
    φ (aeval g P) = aeval (fun i => φ (g i)) P := by
  induction P using MvPolynomial.induction_on with
  | C z => simp only [eq_intCast, map_intCast]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, hP, aeval_X]

variable (a b c : Composition n) (N : ℕ) (I : IntervalPartition n)

/-- The relabelling of the variables of `quiverOf a b c N I` by their positions in
`{0, …, n − 1}`. -/
def quiverEquiv : Fin (quiverOf a b c N I).n ≃ Fin n := I.blockEquiv

@[simp] theorem quiverEquiv_pos (p : Fin (quiverOf a b c N I).s)
    (k : Fin ((quiverOf a b c N I).dim p)) :
    quiverEquiv a b c N I ((quiverOf a b c N I).pos p k) = I.embedding p k :=
  I.blockEquiv_pos p k

@[simp] theorem quiverEquiv_levi_pos (p : Fin (quiverOf a b c N I).s)
    (k : Fin ((quiverOf a b c N I).dim p)) :
    quiverEquiv a b c N I (Levi.pos (quiverOf a b c N I).dim p k) = I.embedding p k :=
  I.blockEquiv_pos p k

theorem rootCoordinateEmbedding_weylPoly :
    rootCoordinateEmbedding (weylPoly I) =
      Family.laurentRelabel (quiverEquiv a b c N I) (quiverOf a b c N I).leviWeylFactor := by
  simp only [weylPoly, ForwardQuiver.leviWeylFactor, Levi.weylFactor, map_prod, map_sub, map_one,
    laurentRelabel_positiveRoot, quiverEquiv]
  refine Finset.prod_congr rfl fun p _ => Finset.prod_congr rfl fun k _ =>
    Finset.prod_congr rfl fun l hl => ?_
  have hkl : k < l := (Finset.mem_filter.mp hl).2
  rw [rootCoordinateEmbedding_monomial_rootDegree ((I.embedding p).lt_iff_lt.mpr hkl),
    I.blockEquiv_pos p k, I.blockEquiv_pos p l]

theorem rootCoordinateEmbedding_arrowPoly (B : ℕ) (e : (quiverOf a b c N I).Arrow) :
    rootCoordinateEmbedding
        (arrowPoly I B ((quiverOf a b c N I).src e) ((quiverOf a b c N I).tgt e)) =
      ∑ m ∈ Finset.range (B + 1),
        Family.laurentRelabel (quiverEquiv a b c N I)
          (aeval ((quiverOf a b c N I).arrowMonomial e)
            (hsymm (Fin ((quiverOf a b c N I).dim ((quiverOf a b c N I).src e)) ×
              Fin ((quiverOf a b c N I).dim ((quiverOf a b c N I).tgt e))) ℤ m)) := by
  simp only [arrowPoly, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_aeval_int, map_aeval_int]
  congr 1
  congr 1
  funext kl
  have hlt := I.embedding_lt_embedding ((quiverOf a b c N I).src_lt_tgt e) kl.1 kl.2
  rw [rootCoordinateEmbedding_monomial_rootDegree hlt, ForwardQuiver.arrowMonomial,
    laurentRelabel_positiveRoot, quiverEquiv_pos, quiverEquiv_pos]

/-- The Levi weight read in the positions `0, …, n − 1` is the residual `c − a − b`. -/
theorem blockWeight_leviWeight :
    (fun k => Window.residual a b c (quiverEquiv a b c N I k)) =
      Levi.blockWeight (quiverOf a b c N I).dim (leviWeight a b c I) := by
  funext k
  simp only [quiverEquiv, Levi.blockWeight, leviWeight]
  exact congrArg (fun x => Window.residual a b c (I.embedding _ x)) (Fin.rev_rev _).symm

end Relabel

/-! ## Theorem 5.3 at the level of characters -/

section Main

variable {a b c : Composition n} {N : ℕ} {I : IntervalPartition n}

/-- Every prefix height is at most `∑_j |ν_j|`. -/
theorem heightDegree_le_sum_abs (i : Fin (n - 1)) :
    (Window.heightDegree a b c i : ℤ) ≤ ∑ j, |Window.residual a b c j| := by
  rw [Window.heightDegree_apply]
  have hx : Window.prefixHeight a b c (i.val + 1) ≤ ∑ j, |Window.residual a b c j| := by
    unfold Window.prefixHeight
    calc ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val + 1), Window.residual a b c j
        ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val + 1),
            |Window.residual a b c j| := Finset.sum_le_sum fun j _ => le_abs_self _
      _ ≤ ∑ j, |Window.residual a b c j| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun j _ _ => abs_nonneg _
  have hS : 0 ≤ ∑ j, |Window.residual a b c j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  omega

/-- The degree bound of the Levi weight dominates every prefix height. -/
theorem heightDegree_le_degreeBound (i : Fin (n - 1)) :
    Window.heightDegree a b c i ≤ (quiverOf a b c N I).degreeBound (leviWeight a b c I) := by
  have hB : ((quiverOf a b c N I).degreeBound (leviWeight a b c I) : ℤ) =
      ∑ j, |Window.residual a b c j| := by
    change ((∑ p : Fin I.length, ∑ k : Fin (I.blocksFun p),
      (leviWeight a b c I p k).natAbs : ℕ) : ℤ) = _
    simp only [Nat.cast_sum, Int.natCast_natAbs, leviWeight]
    rw [← _root_.Composition.sum_sum_apply_embedding (fun j => |Window.residual a b c j|) I]
    refine Finset.sum_congr rfl fun p _ => ?_
    exact Equiv.sum_comp Fin.revPerm (fun k => |Window.residual a b c (I.embedding p k)|)
  rw [Window.heightDegree_apply, Int.toNat_le, hB, Window.prefixHeight]
  calc ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val + 1), Window.residual a b c j
      ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val + 1),
          |Window.residual a b c j| := Finset.sum_le_sum fun j _ => le_abs_self _
    _ ≤ ∑ j, |Window.residual a b c j| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun j _ _ => abs_nonneg _

/-- The multiplicity as one coefficient of the Levi Weyl factor times the characters of the graded
pieces in the degree box. -/
theorem multiplicity_eq_coeff (Q : ForwardQuiver) (lam : Q.Weight) :
    Q.multiplicity lam =
      (Q.leviWeylFactor * ∑ ℓ ∈ Fintype.piFinset (fun _ : Q.Arrow =>
          Finset.range (Q.degreeBound lam + 1)), Q.gradedCharacter ℓ).coeff
        (Levi.blockWeight Q.dim lam) := by
  rw [ForwardQuiver.multiplicity, Finset.mul_sum, AddMonoidAlgebra.coeff_sum,
    Finsupp.coe_finsetSum, Finset.sum_apply]
  rfl

/-- The window comparison: the vertex Weyl factors times the root series of the arrows, and the
vertex Weyl factors times the truncated characters of the arrows, agree in every coefficient below
`β` when `β` is bounded by the truncation degree. -/
theorem weylPoly_mul_arrowPoly_window (B : ℕ) (β : RootDegree n) (hB : ∀ i, β i ≤ B) :
    WindowEq β
      ((weylPoly I * ∏ e : (quiverOf a b c N I).Arrow,
          arrowPoly I B ((quiverOf a b c N I).src e) ((quiverOf a b c N I).tgt e) :
        MvPolynomial (Fin (n - 1)) ℤ) : MvPowerSeries (Fin (n - 1)) ℤ)
      ((weylPoly I : MvPowerSeries (Fin (n - 1)) ℤ) *
        ∏ e : (quiverOf a b c N I).Arrow,
          arrowSeries I ((quiverOf a b c N I).src e) ((quiverOf a b c N I).tgt e)) := by
  have he : ((weylPoly I * ∏ e : (quiverOf a b c N I).Arrow,
      arrowPoly I B ((quiverOf a b c N I).src e) ((quiverOf a b c N I).tgt e) :
        MvPolynomial (Fin (n - 1)) ℤ) : MvPowerSeries (Fin (n - 1)) ℤ) =
      (weylPoly I : MvPowerSeries (Fin (n - 1)) ℤ) *
        ∏ e : (quiverOf a b c N I).Arrow,
          (arrowPoly I B ((quiverOf a b c N I).src e) ((quiverOf a b c N I).tgt e) :
            MvPowerSeries (Fin (n - 1)) ℤ) := by
    change MvPolynomial.coeToMvPowerSeries.ringHom _ = _
    rw [map_mul, map_prod]
    rfl
  rw [he]
  exact (WindowEq.refl _ _).mul (WindowEq.prod β Finset.univ _ _
    fun e _ => arrowPoly_window I B ((quiverOf a b c N I).src_lt_tgt e) β hB)

/-- The atom coefficient of a quiver partition as a Laurent coefficient: the vertex Weyl factors
times the truncated arrow characters, read at `ν = c − a − b`. Any truncation degree bounding the
prefix heights may be used. -/
theorem atomCoefficient_eq_coeff_arrowPoly (h : IsQuiverPartition a b c N I) (B : ℕ)
    (hB : ∀ i, Window.heightDegree a b c i ≤ B) :
    atomCoefficient (key a * key b) c =
      (rootCoordinateEmbedding (weylPoly I * ∏ e : (quiverOf a b c N I).Arrow,
        arrowPoly I B ((quiverOf a b c N I).src e) ((quiverOf a b c N I).tgt e))).coeff
        (Window.residual a b c) := by
  have hw := weylPoly_mul_arrowPoly_window (a := a) (b := b) (c := c) (N := N) (I := I) B
    (Window.heightDegree a b c) hB
  rw [Window.window_rational_extraction h.hyp, rootProduct_eq h,
    ← hw (Window.heightDegree a b c) le_rfl, MvPolynomial.coeff_coe,
    ← coeff_rootCoordinateEmbedding,
    Window.rootWeight_heightDegree h.hyp.balance h.hyp.height_nonneg]

/-- **Theorem 5.3 of the paper, at the level of characters** (`thm:quiver-coefficient`, (5.4)): for
a quiver partition `I` of `(a, b, c)` with `N ≥ max c`, the atom coefficient `[𝒜_c](κ_a κ_b)` is the
multiplicity of `⊗_p V_p^{λ^{(p)}}` in the coordinate ring of the representation space of the quiver
`quiverOf a b c N I`, summed over graded pieces. -/
theorem atomCoefficient_eq_multiplicity (h : IsQuiverPartition a b c N I) :
    atomCoefficient (key a * key b) c =
      (quiverOf a b c N I).multiplicity (leviWeight a b c I) := by
  rw [atomCoefficient_eq_coeff_arrowPoly h _ heightDegree_le_degreeBound, multiplicity_eq_coeff,
    ← blockWeight_leviWeight a b c N I,
    ← Family.laurentRelabel_coefficient (quiverEquiv a b c N I) _ (Window.residual a b c)]
  refine congrArg (fun f : Laurent n => f.coeff (Window.residual a b c)) ?_
  rw [map_mul, map_mul, rootCoordinateEmbedding_weylPoly a b c N I, map_prod, map_sum]
  congr 1
  simp only [rootCoordinateEmbedding_arrowPoly, ForwardQuiver.gradedCharacter, map_prod]
  rw [Finset.prod_univ_sum]

end Main

end

end Schubert.RS.Quiver
