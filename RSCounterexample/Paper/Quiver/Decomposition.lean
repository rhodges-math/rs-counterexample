import RSCounterexample.Paper.Quiver.Schur.Cauchy
import RSCounterexample.Paper.Quiver.Schur.Chains
import RSCounterexample.Paper.Quiver.Levi

/-!
# The Littlewood–Richardson decomposition of quiver multiplicities

For a forward quiver `Q` and a weight `λ` that is dominant on every vertex, the multiplicity of
`⊗_p V_p^{λ^{(p)}}` in the coordinate ring `R_Q` counts the following data
(`ForwardQuiver.multiplicity_eq_card`):
- a Young diagram `μ_e` with at most `min(d_p, d_q)` rows for every arrow `e : p → q`
  (`ForwardQuiver.ArrowShapes`);
- at every vertex `p`, an LR chain for the factors of `p` ending at `λ^{(p)}`.

The factors of `p`, in the order of the outgoing and then the incoming arrows
(`ForwardQuiver.vertexFactors`), are:
- `s_{μ_e}` for an outgoing arrow `e`;
- `s_{μ_e}(x^{−1}) = det^{−μ_{e,0}} s_{μ_e^c}` for an incoming arrow `e`, where `μ_e^c` is the
  complement of `μ_e` in the `d_p × μ_{e,0}` rectangle.

In particular the multiplicity is nonnegative (`ForwardQuiver.multiplicity_nonneg`).

Proof. By the graded Cauchy identity (`Schubert.RS.Quiver.Schur.hsymm_mul_alphabet`), the
character `h_{ℓ_e}(x_i/x_j)` of `Sym^{ℓ_e}(V_p ⊗ V_q^*)` is
`∑_{|μ_e| = ℓ_e} s_{μ_e}(x_{I_p}) s_{μ_e}(x_{I_q}^{−1})`. Regroup the product over the arrows by
vertices. The Levi Weyl projector of a block-separated product is the product of the vertex
projectors (`Levi.schurCoeff_prod_embedBlock`), and the vertex projectors count LR chains
(`Schubert.RS.Quiver.Schur.weylProjector_prod_character`).

## Main definitions

* `ForwardQuiver.outArrows`, `ForwardQuiver.inArrows`, `ForwardQuiver.valence`.
* `ForwardQuiver.ArrowShapes`, `ForwardQuiver.outFactor`, `ForwardQuiver.inFactor`,
  `ForwardQuiver.vertexFactors`.

## Main results

* `ForwardQuiver.aeval_arrowMonomial_hsymm`: the graded Cauchy identity for an arrow.
* `ForwardQuiver.schurCoeff_gradedCharacter_eq_sum`: the LR-sum formula for a graded piece.
* `ForwardQuiver.multiplicity_eq_card`, `ForwardQuiver.multiplicity_nonneg`,
  `ForwardQuiver.schurCoeff_gradedCharacter_nonneg`.
-/

namespace Schubert.RS.Quiver.ForwardQuiver

noncomputable section

open MvPolynomial Schubert.RS.Quiver.Schur

variable (Q : ForwardQuiver)

/-! ## Arrows at a vertex -/

/-- The arrows out of `p`, ordered by their target and then their index. -/
def outArrows (p : Fin Q.s) : List Q.Arrow :=
  (List.finRange Q.s).flatMap fun q => (List.finRange (Q.arrows p q)).map fun k => ⟨(p, q), k⟩

/-- The arrows into `p`, ordered by their source and then their index. -/
def inArrows (p : Fin Q.s) : List Q.Arrow :=
  (List.finRange Q.s).flatMap fun q => (List.finRange (Q.arrows q p)).map fun k => ⟨(q, p), k⟩

theorem mem_outArrows {p : Fin Q.s} {e : Q.Arrow} : e ∈ Q.outArrows p ↔ Q.src e = p := by
  obtain ⟨⟨p', q⟩, k⟩ := e
  simp only [outArrows, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and, src]
  constructor
  · rintro ⟨q', k', h⟩
    cases h
    rfl
  · rintro rfl
    exact ⟨q, k, rfl⟩

theorem mem_inArrows {p : Fin Q.s} {e : Q.Arrow} : e ∈ Q.inArrows p ↔ Q.tgt e = p := by
  obtain ⟨⟨q, p'⟩, k⟩ := e
  simp only [inArrows, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and, tgt]
  constructor
  · rintro ⟨q', k', h⟩
    cases h
    rfl
  · rintro rfl
    exact ⟨q, k, rfl⟩

theorem nodup_outArrows (p : Fin Q.s) : (Q.outArrows p).Nodup := by
  rw [outArrows, List.nodup_flatMap]
  refine ⟨fun q _ => List.Nodup.map (fun k k' h => ?_) (List.nodup_finRange _),
    (List.nodup_finRange _).pairwise_of_forall_ne fun q _ q' _ hne => ?_⟩
  · simpa using h
  · rw [Function.onFun, List.disjoint_left]
    simp only [List.mem_map, List.mem_finRange, true_and]
    rintro e ⟨k, rfl⟩ ⟨k', h⟩
    exact hne (congrArg (fun e : Q.Arrow => e.1.2) h).symm

theorem nodup_inArrows (p : Fin Q.s) : (Q.inArrows p).Nodup := by
  rw [inArrows, List.nodup_flatMap]
  refine ⟨fun q _ => List.Nodup.map (fun k k' h => ?_) (List.nodup_finRange _),
    (List.nodup_finRange _).pairwise_of_forall_ne fun q _ q' _ hne => ?_⟩
  · simpa using h
  · rw [Function.onFun, List.disjoint_left]
    simp only [List.mem_map, List.mem_finRange, true_and]
    rintro e ⟨k, rfl⟩ ⟨k', h⟩
    exact hne (congrArg (fun e : Q.Arrow => e.1.1) h).symm

theorem toFinset_outArrows (p : Fin Q.s) :
    (Q.outArrows p).toFinset = Finset.univ.filter fun e => Q.src e = p := by
  ext e
  simp [mem_outArrows]

theorem toFinset_inArrows (p : Fin Q.s) :
    (Q.inArrows p).toFinset = Finset.univ.filter fun e => Q.tgt e = p := by
  ext e
  simp [mem_inArrows]

/-- The number of arrows at `p`, outgoing and incoming. -/
def valence (p : Fin Q.s) : ℕ := (Q.outArrows p).length + (Q.inArrows p).length

/-! ## Arrow shapes and vertex factors -/

/-- **The Cauchy variables**: one Young diagram per arrow `e : p → q`, with at most `min(d_p, d_q)`
rows. -/
abbrev ArrowShapes : Type :=
  (e : Q.Arrow) → {μ : YoungDiagram // μ.colLen 0 ≤ min (Q.dim (Q.src e)) (Q.dim (Q.tgt e))}

/-- The factor `s_μ` of an outgoing arrow. -/
def outFactor (μ : YoungDiagram) : VertexFactor := ⟨μ, 0⟩

/-- The factor `s_μ(x^{−1}) = det^{−μ_0} s_{μ^c}` of an incoming arrow at a vertex of dimension
`d`: the rational Schur polynomial of the dual weight `(−μ_{d−1}, …, −μ_0)`. -/
def inFactor (d : ℕ) (μ : YoungDiagram) : VertexFactor :=
  ⟨(dualWeight (TauCeti.weightOfShape d μ)).detShiftShape,
    (dualWeight (TauCeti.weightOfShape d μ)).detShift⟩

/-- The rows of the complement: row `r < d` of `μ^c` has `μ_0 − μ_{d−1−r}` cells. -/
theorem rowLen_inFactor_shape (d : ℕ) (μ : YoungDiagram) {r : ℕ} (hr : r < d) :
    (inFactor d μ).shape.rowLen r = μ.rowLen 0 - μ.rowLen (d - 1 - r) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hr
  rw [inFactor, show r = ((⟨r, by omega⟩ : Fin (r + m + 1)) : ℕ) from rfl,
    TauCeti.DominantWeight.rowLen_detShiftShape, TauCeti.DominantWeight.detShift_succ]
  simp only [dualWeight, TauCeti.weightOfShape_apply, Fin.val_rev, Fin.val_last]
  have e1 : r + m + 1 - (r + 1) = m := by omega
  have e2 : r + m + 1 - 1 - r = m := by omega
  have e3 : r + m + 1 - (r + m + 1) = 0 := by omega
  rw [e1, e2, e3]
  have h1 : μ.rowLen m ≤ μ.rowLen 0 := μ.rowLen_anti 0 _ (Nat.zero_le _)
  omega

/-- The power of the determinant in `s_μ(x^{−1})` is `−μ_0`. -/
theorem shift_inFactor (d : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ d) :
    (inFactor d μ).shift = -(μ.rowLen 0 : ℤ) := by
  cases d with
  | zero =>
    have : μ.rowLen 0 = 0 := YoungDiagram.rowLen_eq_zero_of_colLen_le (by omega)
    simp [inFactor, TauCeti.DominantWeight.detShift_eq_zero_of_isEmpty, this]
  | succ d =>
    rw [inFactor, TauCeti.DominantWeight.detShift_succ]
    simp [dualWeight, TauCeti.weightOfShape_apply]

theorem character_outFactor (d : ℕ) (μ : YoungDiagram) :
    (outFactor μ).character d = toLaurent (TauCeti.diagramSchurPoly d ℤ μ) := by
  rw [VertexFactor.character, outFactor, shiftedSchur]
  have : (fun _ : Fin d => (0 : ℤ)) = 0 := rfl
  simp only [this, ← AddMonoidAlgebra.one_def, one_mul]

theorem character_inFactor (d : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ d) :
    (inFactor d μ).character d = reverseNeg (toLaurent (TauCeti.diagramSchurPoly d ℤ μ)) := by
  rw [toLaurent_diagramSchurPoly_eq_ratSchur μ hμ, reverseNeg_ratSchur]
  rfl

/-- The factors at a vertex, outgoing arrows first. -/
def vertexFactorList (μ : Q.ArrowShapes) (p : Fin Q.s) : List VertexFactor :=
  (Q.outArrows p).map (fun e => outFactor (μ e).1) ++
    (Q.inArrows p).map fun e => inFactor (Q.dim p) (μ e).1

theorem length_vertexFactorList (μ : Q.ArrowShapes) (p : Fin Q.s) :
    (Q.vertexFactorList μ p).length = Q.valence p := by
  simp [vertexFactorList, valence]

/-- **The factors at a vertex** `p`: `s_{μ_e}` for the outgoing arrows, then
`det^{−μ_{e,0}} s_{μ_e^c}` for the incoming ones. -/
def vertexFactors (μ : Q.ArrowShapes) (p : Fin Q.s) (t : Fin (Q.valence p)) : VertexFactor :=
  (Q.vertexFactorList μ p)[t.1]'(by rw [length_vertexFactorList]; exact t.isLt)

theorem prod_vertexFactors_character (μ : Q.ArrowShapes) (p : Fin Q.s) :
    ∏ t, (Q.vertexFactors μ p t).character (Q.dim p) =
      (∏ e ∈ Finset.univ.filter (fun e => Q.src e = p), (outFactor (μ e).1).character (Q.dim p)) *
        ∏ e ∈ Finset.univ.filter (fun e => Q.tgt e = p),
          (inFactor (Q.dim p) (μ e).1).character (Q.dim p) := by
  classical
  rw [Fintype.prod_equiv (finCongr (length_vertexFactorList Q μ p).symm)
    (fun t => (Q.vertexFactors μ p t).character (Q.dim p))
    (fun t' => ((Q.vertexFactorList μ p)[t'.1]).character (Q.dim p)) fun t => rfl]
  refine (Fin.prod_univ_fun_getElem (Q.vertexFactorList μ p)
    (fun F : VertexFactor => F.character (Q.dim p))).trans ?_
  rw [vertexFactorList, List.map_append, List.prod_append, List.map_map, List.map_map,
    ← toFinset_outArrows, ← toFinset_inArrows, List.prod_toFinset _ (Q.nodup_outArrows p),
    List.prod_toFinset _ (Q.nodup_inArrows p)]
  rfl

/-! ## The graded Cauchy identity for an arrow -/

/-- `x_i ↦ x_i` for the variables of the source block, `y_j ↦ x_{rev j}^{−1}` for those of the
target block. -/
def arrowHom (e : Q.Arrow) : XY (Q.dim (Q.src e)) (Q.dim (Q.tgt e)) →+* Laurent Q.n :=
  eval₂Hom ((Levi.embedBlock Q.dim (Q.src e)).comp toLaurent)
    fun j => AddMonoidAlgebra.single (-Pi.single (Q.pos (Q.tgt e) (Fin.rev j)) 1) 1

theorem embedBlock_toLaurent_X (p : Fin Q.s) (i : Fin (Q.dim p)) :
    Levi.embedBlock Q.dim p (toLaurent (X i)) =
      AddMonoidAlgebra.single (Pi.single (Q.pos p i) 1) 1 := by
  rw [toLaurent_X, Levi.embedBlock_single, Levi.blockSplit_single_single]

theorem arrowHom_aeval_hsymm (e : Q.Arrow) (ℓ : ℕ) :
    Q.arrowHom e (aeval (R := ℤ) (xyProd (Q.dim (Q.src e)) (Q.dim (Q.tgt e)))
      (hsymm (Fin (Q.dim (Q.src e)) × Fin (Q.dim (Q.tgt e))) ℤ ℓ)) =
      aeval (Q.arrowMonomial e) (hsymm _ ℤ ℓ) := by
  have h1 : (Q.arrowHom e).comp
      (aeval (R := ℤ) (xyProd (Q.dim (Q.src e)) (Q.dim (Q.tgt e)))).toRingHom =
      (aeval (R := ℤ) fun ij : Fin (Q.dim (Q.src e)) × Fin (Q.dim (Q.tgt e)) =>
        Q.arrowMonomial e (ij.1, Fin.rev ij.2)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro z
      exact RingHom.congr_fun (RingHom.ext_int (((Q.arrowHom e).comp
        (aeval (R := ℤ) (xyProd (Q.dim (Q.src e)) (Q.dim (Q.tgt e)))).toRingHom).comp C)
        ((aeval (R := ℤ) fun ij : Fin (Q.dim (Q.src e)) × Fin (Q.dim (Q.tgt e)) =>
          Q.arrowMonomial e (ij.1, Fin.rev ij.2)).toRingHom.comp C)) z
    · intro ij
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        aeval_X, xyProd, map_mul, arrowHom, eval₂Hom_C, eval₂Hom_X', RingHom.comp_apply,
        embedBlock_toLaurent_X, arrowMonomial, positiveRoot, AddMonoidAlgebra.single_mul_single,
        mul_one, sub_eq_add_neg]
  have h2 := RingHom.congr_fun h1 (hsymm _ ℤ ℓ)
  simp only [RingHom.coe_comp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Function.comp_apply] at h2
  rw [h2]
  have h3 := aeval_rename (g := Q.arrowMonomial e)
    (k := ⇑((Equiv.refl _).prodCongr (Fin.revPerm : Equiv.Perm (Fin (Q.dim (Q.tgt e)))) :
      Fin (Q.dim (Q.src e)) × Fin (Q.dim (Q.tgt e)) ≃ _))
    (p := hsymm (Fin (Q.dim (Q.src e)) × Fin (Q.dim (Q.tgt e))) ℤ ℓ)
  rw [rename_hsymm] at h3
  rw [h3]
  rfl

theorem arrowHom_C (e : Q.Arrow) (P : MvPolynomial (Fin (Q.dim (Q.src e))) ℤ) :
    Q.arrowHom e (C P) = Levi.embedBlock Q.dim (Q.src e) (toLaurent P) :=
  eval₂Hom_C _ _ _

theorem reverseNegWeight_pi_single {d : ℕ} (j : Fin d) :
    reverseNegWeight (Pi.single j (1 : ℤ) : Schubert.RS.Weight d) = Pi.single (Fin.rev j) (-1) := by
  funext i
  change -(Pi.single j (1 : ℤ) : Schubert.RS.Weight d) i.rev = _
  by_cases hi : i = Fin.rev j
  · subst hi
    simp
  · have h : i.rev ≠ j := fun h => hi (by rw [← h, Fin.rev_rev])
    rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne hi, neg_zero]

theorem arrowHom_map (e : Q.Arrow) (P : MvPolynomial (Fin (Q.dim (Q.tgt e))) ℤ) :
    Q.arrowHom e (map (algebraMap ℤ (MvPolynomial (Fin (Q.dim (Q.src e))) ℤ)) P) =
      Levi.embedBlock Q.dim (Q.tgt e) (reverseNeg (toLaurent P)) := by
  set f : MvPolynomial (Fin (Q.dim (Q.tgt e))) ℤ →+* Laurent Q.n :=
    (Q.arrowHom e).comp (map (algebraMap ℤ (MvPolynomial (Fin (Q.dim (Q.src e))) ℤ)))
  set g : MvPolynomial (Fin (Q.dim (Q.tgt e))) ℤ →+* Laurent Q.n :=
    (Levi.embedBlock Q.dim (Q.tgt e)).comp
      ((reverseNeg : Laurent (Q.dim (Q.tgt e)) ≃+* Laurent (Q.dim (Q.tgt e))).toRingHom.comp
        toLaurent)
  have h : f = g := by
    apply MvPolynomial.ringHom_ext
    · intro z
      exact RingHom.congr_fun (RingHom.ext_int (f.comp C) (g.comp C)) z
    · intro j
      change Q.arrowHom e (map _ (X j)) =
        Levi.embedBlock Q.dim (Q.tgt e) (reverseNeg (toLaurent (X j)))
      rw [map_X, arrowHom, eval₂Hom_X', toLaurent_X, Schubert.RS.reverseNeg_single,
        Levi.embedBlock_single, reverseNegWeight_pi_single, Levi.blockSplit_single_single,
        Pi.single_neg]
  exact RingHom.congr_fun h P

/-- **The graded Cauchy identity for an arrow** `e : p → q`:
`h_ℓ(x_i/x_j) = ∑_μ s_μ(x_{I_p}) s_μ(x_{I_q}^{−1})`, over the shapes with `ℓ` cells and at most
`min(d_p, d_q)` rows. -/
theorem aeval_arrowMonomial_hsymm (e : Q.Arrow) (ℓ : ℕ) :
    aeval (Q.arrowMonomial e) (hsymm (Fin (Q.dim (Q.src e)) × Fin (Q.dim (Q.tgt e))) ℤ ℓ) =
      ∑ μ ∈ shapesOfSize ℓ (min (Q.dim (Q.src e)) (Q.dim (Q.tgt e))),
        Levi.embedBlock Q.dim (Q.src e) ((outFactor μ).character (Q.dim (Q.src e))) *
          Levi.embedBlock Q.dim (Q.tgt e) ((inFactor (Q.dim (Q.tgt e)) μ).character
            (Q.dim (Q.tgt e))) := by
  rw [← arrowHom_aeval_hsymm, hsymm_mul_alphabet, map_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hμb : μ.colLen 0 ≤ Q.dim (Q.tgt e) := (mem_shapesOfSize.mp hμ).2.trans (min_le_right _ _)
  rw [map_mul, arrowHom_C, arrowHom_map, character_outFactor, character_inFactor _ μ hμb]

/-! ## Regrouping by vertices -/

/-- The part at the vertex `p` of the factor of the arrow `e`: `s_{μ_e}` if `e` leaves `p`,
`s_{μ_e}(x^{−1})` if `e` enters `p`, `1` otherwise. -/
def arrowFactor (μ : Q.ArrowShapes) (p : Fin Q.s) (e : Q.Arrow) : Laurent (Q.dim p) :=
  (if Q.src e = p then (outFactor (μ e).1).character (Q.dim p) else 1) *
    (if Q.tgt e = p then (inFactor (Q.dim p) (μ e).1).character (Q.dim p) else 1)

theorem prod_embedBlock_arrowFactor (μ : Q.ArrowShapes) (e : Q.Arrow) :
    ∏ p, Levi.embedBlock Q.dim p (Q.arrowFactor μ p e) =
      Levi.embedBlock Q.dim (Q.src e) ((outFactor (μ e).1).character (Q.dim (Q.src e))) *
        Levi.embedBlock Q.dim (Q.tgt e) ((inFactor (Q.dim (Q.tgt e)) (μ e).1).character
          (Q.dim (Q.tgt e))) := by
  classical
  simp only [arrowFactor, map_mul, apply_ite (Levi.embedBlock Q.dim _), map_one]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq, Finset.prod_ite_eq]
  simp

theorem prod_arrowFactor (μ : Q.ArrowShapes) (p : Fin Q.s) :
    ∏ e, Q.arrowFactor μ p e = ∏ t, (Q.vertexFactors μ p t).character (Q.dim p) := by
  classical
  rw [prod_vertexFactors_character]
  simp only [arrowFactor]
  rw [Finset.prod_mul_distrib, ← Finset.prod_filter, ← Finset.prod_filter]

/-! ## The LR-sum formula -/

/-- The arrow shapes with `|μ_e| = ℓ_e` for every arrow. -/
def shapesOfDegree (ℓ : Q.Arrow → ℕ) : Finset Q.ArrowShapes :=
  Fintype.piFinset fun e =>
    (shapesOfSize (ℓ e) (min (Q.dim (Q.src e)) (Q.dim (Q.tgt e)))).subtype _

theorem mem_shapesOfDegree {ℓ : Q.Arrow → ℕ} {μ : Q.ArrowShapes} :
    μ ∈ Q.shapesOfDegree ℓ ↔ ∀ e, (μ e).1.card = ℓ e := by
  simp only [shapesOfDegree, Fintype.mem_piFinset, Finset.mem_subtype, mem_shapesOfSize]
  exact forall_congr' fun e => and_iff_left (μ e).2

/-- **The graded character as a sum over arrow shapes** of block-separated products of vertex
factors. -/
theorem gradedCharacter_eq_sum (ℓ : Q.Arrow → ℕ) :
    Q.gradedCharacter ℓ = ∑ μ ∈ Q.shapesOfDegree ℓ,
      ∏ p, Levi.embedBlock Q.dim p (∏ t, (Q.vertexFactors μ p t).character (Q.dim p)) := by
  classical
  rw [gradedCharacter]
  simp only [aeval_arrowMonomial_hsymm]
  rw [Finset.prod_congr rfl fun e _ => (Finset.sum_subtype_of_mem (fun μ =>
      Levi.embedBlock Q.dim (Q.src e) ((outFactor μ).character (Q.dim (Q.src e))) *
        Levi.embedBlock Q.dim (Q.tgt e) ((inFactor (Q.dim (Q.tgt e)) μ).character
          (Q.dim (Q.tgt e))))
      (p := fun μ : YoungDiagram => μ.colLen 0 ≤ min (Q.dim (Q.src e)) (Q.dim (Q.tgt e)))
      fun μ hμ => (mem_shapesOfSize.mp hμ).2).symm, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← Finset.prod_congr rfl fun e _ => Q.prod_embedBlock_arrowFactor μ e, Finset.prod_comm]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← map_prod, prod_arrowFactor]

/-- **The LR-sum formula for a graded piece**: for `λ` dominant on every vertex, the multiplicity
of `⊗_p V_p^{λ^{(p)}}` in the graded piece of multidegree `ℓ` is
`∑_{|μ_e| = ℓ_e} ∏_p #LRChain(factors of p, λ^{(p)})`. -/
theorem schurCoeff_gradedCharacter_eq_sum (ℓ : Q.Arrow → ℕ) {lam : Q.Weight}
    (hlam : Q.IsDominant lam) :
    Q.schurCoeff (Q.gradedCharacter ℓ) lam = ∑ μ ∈ Q.shapesOfDegree ℓ,
      ∏ p, (Fintype.card (LRChain (Q.vertexFactors μ p) (lam p)) : ℤ) := by
  rw [gradedCharacter_eq_sum, schurCoeff, Levi.schurCoeff_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Levi.schurCoeff_prod_embedBlock]
  refine Finset.prod_congr rfl fun p _ => ?_
  exact weylProjector_prod_character (Q.vertexFactors μ p) ⟨lam p, hlam p⟩

theorem schurCoeff_gradedCharacter_nonneg (ℓ : Q.Arrow → ℕ) {lam : Q.Weight}
    (hlam : Q.IsDominant lam) : 0 ≤ Q.schurCoeff (Q.gradedCharacter ℓ) lam := by
  rw [Q.schurCoeff_gradedCharacter_eq_sum ℓ hlam]
  exact Finset.sum_nonneg fun μ _ => Finset.prod_nonneg fun p _ => Nat.cast_nonneg _

/-! ## The multiplicity counts LR data -/

/-- The LR data at all vertices for given arrow shapes. -/
abbrev VertexChains (μ : Q.ArrowShapes) (lam : Q.Weight) : Type :=
  (p : Fin Q.s) → LRChain (Q.vertexFactors μ p) (lam p)

/-- The sizes `|μ_e|` of arrow shapes. -/
def shapeDegree (μ : Q.ArrowShapes) (e : Q.Arrow) : ℕ := (μ e).1.card

theorem mem_shapesOfDegree_shapeDegree (μ : Q.ArrowShapes) :
    μ ∈ Q.shapesOfDegree (Q.shapeDegree μ) :=
  (Q.mem_shapesOfDegree).mpr fun _ => rfl

open scoped Classical in
/-- Arrow shapes too large for the cut-degree bound carry no LR data. -/
theorem isEmpty_vertexChains {lam : Q.Weight} (hlam : Q.IsDominant lam) (μ : Q.ArrowShapes)
    (hμ : μ ∉ (Fintype.piFinset fun _ : Q.Arrow => Finset.range (Q.degreeBound lam + 1)).biUnion
      Q.shapesOfDegree) : IsEmpty (Q.VertexChains μ lam) := by
  classical
  have hℓ : Q.shapeDegree μ ∉ Fintype.piFinset fun _ : Q.Arrow =>
      Finset.range (Q.degreeBound lam + 1) := fun h =>
    hμ (Finset.mem_biUnion.mpr ⟨_, h, Q.mem_shapesOfDegree_shapeDegree μ⟩)
  have hcut : ¬ Q.CutDegrees lam (Q.shapeDegree μ) := by
    intro hc
    apply hℓ
    rw [Fintype.mem_piFinset]
    exact fun e => Finset.mem_range.mpr (Nat.lt_succ_of_le (hc.le_degreeBound e))
  have h0 := Q.schurCoeff_gradedCharacter_eq_zero hcut
  rw [Q.schurCoeff_gradedCharacter_eq_sum _ hlam] at h0
  have hμ0 := (Finset.sum_eq_zero_iff_of_nonneg fun μ' _ => Finset.prod_nonneg fun p _ =>
    Nat.cast_nonneg _).mp h0 μ (Q.mem_shapesOfDegree_shapeDegree μ)
  rw [← Nat.cast_prod, Nat.cast_eq_zero, ← Fintype.card_pi] at hμ0
  exact Fintype.card_eq_zero_iff.mp hμ0

open scoped Classical in
/-- The arrow shapes carrying LR data, as a subtype of a finite set. -/
def chainsEquiv {lam : Q.Weight} (hlam : Q.IsDominant lam) :
    (Σ μ : ↥((Fintype.piFinset fun _ : Q.Arrow => Finset.range (Q.degreeBound lam + 1)).biUnion
      Q.shapesOfDegree), Q.VertexChains μ.1 lam) ≃ Σ μ : Q.ArrowShapes, Q.VertexChains μ lam where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, by
    by_contra h
    exact (Q.isEmpty_vertexChains hlam x.1 h).false x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finite_chains {lam : Q.Weight} (hlam : Q.IsDominant lam) :
    Finite (Σ μ : Q.ArrowShapes, Q.VertexChains μ lam) :=
  Finite.of_equiv _ (Q.chainsEquiv hlam)

open scoped Classical in
/-- **Theorem 5.3, the explicit LR-sum formula**: for a weight `λ` dominant on every vertex, the
multiplicity of `⊗_p V_p^{λ^{(p)}}` in `R_Q` is the number of pairs `(μ, T)` of arrow shapes and,
at every vertex, an LR chain for its factors ending at `λ^{(p)}`. -/
theorem multiplicity_eq_card {lam : Q.Weight} (hlam : Q.IsDominant lam) :
    Q.multiplicity lam = Nat.card (Σ μ : Q.ArrowShapes, Q.VertexChains μ lam) := by
  classical
  set S := (Fintype.piFinset fun _ : Q.Arrow => Finset.range (Q.degreeBound lam + 1)).biUnion
    Q.shapesOfDegree
  rw [← Nat.card_congr (Q.chainsEquiv hlam), Nat.card_eq_fintype_card, Fintype.card_sigma]
  rw [multiplicity]
  simp only [Q.schurCoeff_gradedCharacter_eq_sum _ hlam]
  rw [← Finset.sum_biUnion]
  · push_cast
    rw [Finset.sum_coe_sort S fun μ => ((Fintype.card (Q.VertexChains μ lam) : ℕ) : ℤ)]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Fintype.card_pi, Nat.cast_prod]
  · intro ℓ _ ℓ' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro μ h1 h2
    apply hne
    funext e
    rw [← (Q.mem_shapesOfDegree.mp h1) e, ← (Q.mem_shapesOfDegree.mp h2) e]

/-- **The quiver multiplicity is nonnegative.** -/
theorem multiplicity_nonneg {lam : Q.Weight} (hlam : Q.IsDominant lam) :
    0 ≤ Q.multiplicity lam := by
  rw [Q.multiplicity_eq_card hlam]
  exact Nat.cast_nonneg _

end

end Schubert.RS.Quiver.ForwardQuiver
