import RSCounterexample.GLRep.HighestWeight.Classification
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Irreducible

/-!
# The irreducible polynomial representations: Weyl modules

For a Young diagram `μ` with at most `n` rows, the irreducible polynomial representation
`GLRep.irrep K n μ` of `GL_n(K)` is Tau Ceti's Weyl module of shape `μ`: the image of the Young
symmetrizer `c_t` of the row-superstandard tableau `t` acting on `(Kⁿ)^{⊗|μ|}`. Tau Ceti proves
that it is irreducible in characteristic zero.

Its highest weight vector is `v = c_t (e_{r(1)} ⊗ ⋯ ⊗ e_{r(d)})`, where `r ℓ` is the row of the
label `ℓ` (`GLRep.irrepHighestVector`):

* `v ≠ 0`, because its coordinate at `e_r` is the order of the row group of `t`;
* `v` has weight `μ`, because the torus scales `e_r` by `∏_ℓ t_{r ℓ} = t^μ` and commutes with
  `c_t`;
* the transvections `1 + sE_ab`, `a < b`, fix `v`. Expanding `(1 + sE_ab)^{⊗d} e_r`, every term
  other than `e_r` has a factor `e_a` both at a label of row `b` and at the label of row `a` in
  the same column; the column transposition of these two labels fixes that pure tensor and
  negates `c_t`, so `c_t` kills it.

So `v` is a highest weight vector of weight `μ` for the differential, and the character of
`irrep K n μ` is the Schur polynomial `s_μ` (`GLRep.character_irrep`). Every irreducible
polynomial representation is equivalent to exactly one `irrep K n μ`
(`GLRep.IsPolynomialRep.exists_nonempty_equiv_irrep`, `GLRep.irrep_eq_of_nonempty_equiv`).

## Main definitions

* `GLRep.irrep K n μ`: the irreducible polynomial representation of highest weight `μ`.
* `GLRep.irrepHighestVector K n μ hμ`: its highest weight vector.

## Main results

* `GLRep.isPolynomialRep_stdRep`, `GLRep.isPolynomialRep_tensorPowerRep`,
  `GLRep.isPolynomialRep_irrep`, `GLRep.isIrreducible_irrep`.
* `GLRep.isGlHighestWeightVector_irrepHighestVector`, `GLRep.character_irrep`.
* `GLRep.IsPolynomialRep.exists_nonempty_equiv_irrep`: the classification.
* `GLRep.finrank_intertwiningMap_irrep_self`, `GLRep.finrank_intertwiningMap_irrep_of_ne`.
-/

namespace GLRep

open Module LieModule TauCeti TauCeti.YoungTableau
open scoped Matrix

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-! ### Polynomiality -/

omit [CharZero K] in
/-- The standard representation of `GL_n(K)` is polynomial. -/
theorem isPolynomialRep_stdRep : IsPolynomialRep (stdRep K n) := by
  classical
  refine (hasCoeffsIn_iff_toMatrix (Pi.basisFun K (Fin n))).mpr fun i j => ?_
  convert coord_mem_coordFunctions (glCoord K n) (i, j) using 1
  funext g
  rw [LinearMap.toMatrix_eq_toMatrix', stdRep_apply, ← Matrix.toLin'_apply',
    LinearMap.toMatrix'_toLin', glCoord_apply]

omit [CharZero K] in
/-- The tensor powers of the standard representation are polynomial. -/
theorem isPolynomialRep_tensorPowerRep (d : ℕ) : IsPolynomialRep (tensorPowerRep K n d) :=
  HasCoeffsIn.piTensor fun _ => isPolynomialRep_stdRep

variable (K n) in
/-- The space of the irreducible representation `V(μ)`: the Weyl module of the shape `μ`, a
subspace of `(Kⁿ)^{⊗|μ|}`. -/
def IrrepSpace (μ : YoungDiagram) : Type _ := (weylModuleOfShape K n μ).toSubmodule

instance (μ : YoungDiagram) : AddCommGroup (IrrepSpace K n μ) :=
  inferInstanceAs (AddCommGroup (weylModuleOfShape K n μ).toSubmodule)

instance (μ : YoungDiagram) : Module K (IrrepSpace K n μ) :=
  inferInstanceAs (Module K (weylModuleOfShape K n μ).toSubmodule)

variable (K n) in
/-- The **irreducible polynomial representation** `V(μ)` of `GL_n(K)` of highest weight `μ`: the
Weyl module of the shape `μ`, the image of a Young symmetrizer on `(Kⁿ)^{⊗|μ|}`. -/
def irrep (μ : YoungDiagram) : Representation K (GL (Fin n) K) (IrrepSpace K n μ) :=
  weylRepOfShape K n μ

variable (K n) in
/-- The inclusion of `V(μ)` in `(Kⁿ)^{⊗|μ|}`. -/
def irrepIncl (μ : YoungDiagram) :
    IrrepSpace K n μ →ₗ[K] PiTensorProduct K fun _ : Fin μ.card => Fin n → K :=
  (weylModuleOfShape K n μ).toSubmodule.subtype

theorem irrepIncl_injective (μ : YoungDiagram) : Function.Injective (irrepIncl K n μ) :=
  Subtype.val_injective

theorem irrepIncl_irrep (μ : YoungDiagram) (g : GL (Fin n) K) (x : IrrepSpace K n μ) :
    irrepIncl K n μ (irrep K n μ g x) = tensorPowerRep K n μ.card g (irrepIncl K n μ x) :=
  rfl

theorem isPolynomialRep_irrep (μ : YoungDiagram) : IsPolynomialRep (irrep K n μ) :=
  (isPolynomialRep_tensorPowerRep μ.card).subrepresentation (weylModuleOfShape K n μ)

theorem isIrreducible_irrep {μ : YoungDiagram} (hμ : μ.colLen 0 ≤ n) :
    (irrep K n μ).IsIrreducible :=
  (isIrreducible_weylRepOfShape_iff (k := K) (n := n) μ).mpr hμ

/-- If `ρ(1 + tX)` fixes `w` for all `t`, then the differential `dρ(X)` kills `w`. -/
theorem IsPolynomialRep.lie_eq_zero_of_forall {W : Type*} [AddCommGroup W] [Module K W]
    {ρ : Representation K (GL (Fin n) K) W} (h : IsPolynomialRep ρ)
    (X : Matrix (Fin n) (Fin n) K) (w : W)
    (hw : ∀ t (ht : (1 + t • X).det ≠ 0), ρ (lineGL X t ht) w = w) : h.lie X w = 0 := by
  have := h.lie_apply_eq_of_forall X w one_lt_two (fun k => if k = 0 then w else 0)
    fun t ht => by
      simp [hw]
  simpa using this

/-! ### The Young symmetrizer on tensors -/

section Symmetrizer

variable {μ : YoungDiagram} (t : YoungTableau μ)

omit [CharZero K] in
/-- The Young symmetrizer commutes with the action of `GL_n(K)` on the tensor power. -/
theorem tensorPowerRep_permTensorActionAlgHom (a : MonoidAlgebra K (Equiv.Perm (Fin μ.card)))
    (g : GL (Fin n) K) (x : PiTensorProduct K fun _ : Fin μ.card => Fin n → K) :
    tensorPowerRep K n μ.card g (permTensorActionAlgHom K n μ.card a x) =
      permTensorActionAlgHom K n μ.card a (tensorPowerRep K n μ.card g x) :=
  (LinearMap.congr_fun (commute_permTensorActionAlgHom_tensorPowerRep K n μ.card a g).eq x).symm

/-- **The Young symmetrizer kills a pure tensor with equal factors at two labels of the same
column**: their transposition fixes the tensor and negates `c_t`. -/
theorem permTensorActionAlgHom_youngSymmetrizerOver_tprod_eq_zero
    {x : Fin μ.card → Fin n → K} {ℓ₀ ℓ₁ : Fin μ.card} (hcol : colIndex t ℓ₀ = colIndex t ℓ₁)
    (hne : ℓ₀ ≠ ℓ₁) (hx : x ℓ₀ = x ℓ₁) :
    permTensorActionAlgHom K n μ.card (youngSymmetrizerOver K t) (PiTensorProduct.tprod K x) =
      0 := by
  have hτ : Equiv.swap ℓ₀ ℓ₁ ∈ colSubgroup t := swap_mem_colSubgroup hcol
  have hswap : (fun i => x ((Equiv.swap ℓ₀ ℓ₁).symm i)) = x :=
    funext fun i => by rw [Equiv.symm_swap]; exact Equiv.apply_swap_eq_self hx i
  have h : permTensorActionAlgHom K n μ.card
        (youngSymmetrizerOver K t * MonoidAlgebra.single (Equiv.swap ℓ₀ ℓ₁) 1)
        (PiTensorProduct.tprod K x) =
      permTensorActionAlgHom K n μ.card (youngSymmetrizerOver K t) (PiTensorProduct.tprod K x) := by
    rw [map_mul, Module.End.mul_apply, permTensorActionAlgHom_apply_tprod,
      MonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp), one_smul, hswap]
  have hneg : youngSymmetrizerOver K t * MonoidAlgebra.single (Equiv.swap ℓ₀ ℓ₁) 1 =
      -youngSymmetrizerOver K t := by
    simpa [Equiv.Perm.sign_swap hne] using mul_youngSymmetrizerOver_right K t ⟨_, hτ⟩
  rw [hneg, map_neg, LinearMap.neg_apply] at h
  have h2 : (2 : K) • permTensorActionAlgHom K n μ.card (youngSymmetrizerOver K t)
      (PiTensorProduct.tprod K x) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- Each label of a tableau whose shape has at most `n` rows lies in a row below `n`. -/
theorem rowIndex_lt (hn : μ.colLen 0 ≤ n) (ℓ : Fin μ.card) : rowIndex t ℓ < n := by
  have hmem : ((t.symm ℓ : ℕ × ℕ).1, (t.symm ℓ : ℕ × ℕ).2) ∈ μ := (t.symm ℓ).2
  have h1 := YoungDiagram.mem_iff_lt_colLen.mp hmem
  rw [rowIndex_def]
  exact lt_of_lt_of_le (lt_of_lt_of_le h1 (μ.colLen_anti 0 _ (Nat.zero_le _))) hn

/-- The row of each label, as the index of a basis vector of `Kⁿ`. -/
def rowVector (hn : μ.colLen 0 ≤ n) : Fin μ.card → Fin n :=
  fun ℓ => ⟨rowIndex t ℓ, rowIndex_lt t hn ℓ⟩

/-- Exactly `μ_i` labels lie in row `i`. -/
theorem card_filter_rowVector_eq (hn : μ.colLen 0 ≤ n) (i : Fin n) :
    (Finset.univ.filter fun ℓ => rowVector t hn ℓ = i).card = μ.rowLen i := by
  rw [← Fintype.card_subtype, YoungDiagram.rowLen_eq_card, ← Fintype.card_coe]
  refine Fintype.card_congr ((Equiv.subtypeEquivRight fun ℓ => ?_).trans (rowFiberEquiv t i))
  exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

omit [CharZero K] in
theorem prod_rowVector (hn : μ.colLen 0 ≤ n) (s : Fin n → K) :
    ∏ ℓ, s (rowVector t hn ℓ) = ∏ i : Fin n, s i ^ μ.rowLen i := by
  rw [← Finset.prod_fiberwise_of_maps_to (g := rowVector t hn) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_congr rfl fun ℓ hℓ => by rw [(Finset.mem_filter.mp hℓ).2], Finset.prod_const,
    card_filter_rowVector_eq]

/-- **The symmetrizer does not kill `e_r`**: the coordinate of `c_t e_r` at `e_r` is the order of
the row group. -/
theorem repr_youngSymmetrizerOver_rowVector (hn : μ.colLen 0 ≤ n) :
    (tensorPowerBasis K n μ.card).repr
        (permTensorActionAlgHom K n μ.card (youngSymmetrizerOver K t)
          (tensorPowerBasis K n μ.card (rowVector t hn))) (rowVector t hn) =
      (Nat.card (rowSubgroup t) : K) := by
  classical
  set r := rowVector t hn
  set S : Finset (Equiv.Perm (Fin μ.card)) := {σ | σ ∈ rowSubgroup t} with hSdef
  have hmemS : ∀ σ : Equiv.Perm (Fin μ.card), σ ∈ S ↔ σ ∈ rowSubgroup t := by
    intro σ
    rw [hSdef]
    simp
  have hcond : ∀ σ : Equiv.Perm (Fin μ.card),
      (fun ℓ => r (σ.symm ℓ)) = r ↔ σ ∈ rowSubgroup t := by
    intro σ
    rw [← inv_mem_iff (G := Equiv.Perm (Fin μ.card)), mem_rowSubgroup]
    exact ⟨fun h ℓ => congrArg Fin.val (congrFun h ℓ), fun h => funext fun ℓ => Fin.ext (h ℓ)⟩
  have hSNat : Nat.card (rowSubgroup t) = S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hSNat, permTensorActionAlgHom_apply_tensorPowerBasis, map_sum, Finset.sum_apply']
  have hterm : ∀ σ ∈ (youngSymmetrizerOver K t).coeff.support,
      ((tensorPowerBasis K n μ.card).repr
          ((youngSymmetrizerOver K t).coeff σ •
            tensorPowerBasis K n μ.card fun i => r (σ.symm i))) r =
        if σ ∈ rowSubgroup t then (youngSymmetrizerOver K t).coeff σ else 0 := by
    intro σ _
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.single_apply]
    exact if_congr (hcond σ) rfl rfl
  rw [Finset.sum_congr rfl hterm]
  have hcoeff : ∀ σ ∈ rowSubgroup t, (youngSymmetrizerOver K t).coeff σ = 1 := by
    intro σ hσ
    rw [youngSymmetrizerOver_coeff, youngSymmetrizer_coeff_eq_one_of_mem_rowSubgroup t hσ,
      map_one]
  have hsub : S ⊆ (youngSymmetrizerOver K t).coeff.support := by
    intro σ hσ
    rw [Finsupp.mem_support_iff, hcoeff σ ((hmemS σ).mp hσ)]
    exact one_ne_zero
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hfilter : (youngSymmetrizerOver K t).coeff.support.filter (· ∈ rowSubgroup t) = S := by
    ext σ
    simp only [Finset.mem_filter, hmemS]
    exact ⟨fun h => h.2, fun h => ⟨hsub ((hmemS σ).mpr h), h⟩⟩
  rw [hfilter, Finset.sum_congr rfl fun σ hσ => hcoeff σ ((hmemS σ).mp hσ), Finset.sum_const,
    nsmul_eq_mul, mul_one]

theorem youngSymmetrizerOver_rowVector_ne_zero (hn : μ.colLen 0 ≤ n) :
    permTensorActionAlgHom K n μ.card (youngSymmetrizerOver K t)
      (tensorPowerBasis K n μ.card (rowVector t hn)) ≠ 0 := by
  intro h0
  have h := repr_youngSymmetrizerOver_rowVector (K := K) t hn
  rw [h0, map_zero, Finsupp.zero_apply] at h
  exact Nat.cast_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩) h.symm

omit [CharZero K] in
/-- The torus scales `e_r` by `∏_ℓ t_{r ℓ}`. -/
theorem tensorPowerRep_diagGL_tensorPowerBasis {d : ℕ} (s : Fin n → Kˣ) (f : Fin d → Fin n) :
    tensorPowerRep K n d (diagGL s) (tensorPowerBasis K n d f) =
      (∏ ℓ, (s (f ℓ) : K)) • tensorPowerBasis K n d f := by
  classical
  rw [tensorPowerBasis_apply, Representation.tensorPower_apply, PiTensorProduct.map_tprod,
    ← MultilinearMap.map_smul_univ]
  congr 1
  funext ℓ
  rw [stdRep_apply_apply, diagGL_coe]
  funext j
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases hj : j = f ℓ
  · subst hj
    simp
  · simp [hj]

/-- **The transvections `1 + sE_ab`, `a < b`, fix the highest weight vector.** -/
theorem youngSymmetrizerOver_tensorPowerRep_lineGL (hn : μ.colLen 0 ≤ n) {a b : Fin n}
    (hab : a < b) (s : K) (hs : (1 + s • (matUnit a b : Matrix (Fin n) (Fin n) K)).det ≠ 0) :
    permTensorActionAlgHom K n μ.card (youngSymmetrizerOver K t)
        (tensorPowerRep K n μ.card (lineGL (matUnit a b) s hs)
          (tensorPowerBasis K n μ.card (rowVector t hn))) =
      permTensorActionAlgHom K n μ.card (youngSymmetrizerOver K t)
        (tensorPowerBasis K n μ.card (rowVector t hn)) := by
  classical
  set r := rowVector t hn with hr
  set c := permTensorActionAlgHom K n μ.card (youngSymmetrizerOver K t)
  have hmv : ∀ j : Fin n, (matUnit a b : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j 1 =
      if j = b then Pi.single a 1 else 0 := by
    intro j
    rw [Matrix.single_mulVec]
    funext i
    by_cases hj : j = b
    · subst hj
      simp [Function.update_apply, Pi.single_apply]
    · simp [Function.update_apply, hj, Ne.symm hj]
  let m : Fin μ.card → Fin n → K := fun ℓ => Pi.single (r ℓ) 1
  let m' : Fin μ.card → Fin n → K :=
    fun ℓ => s • ((matUnit a b : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single (r ℓ) 1)
  have hexp : tensorPowerRep K n μ.card (lineGL (matUnit a b) s hs)
      (tensorPowerBasis K n μ.card r) = PiTensorProduct.tprod K (m + m') := by
    rw [tensorPowerBasis_apply, Representation.tensorPower_apply, PiTensorProduct.map_tprod]
    congr 1
    funext ℓ
    rw [stdRep_apply_apply, coe_lineGL, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    rfl
  rw [hexp, MultilinearMap.map_add_univ, map_sum, Finset.sum_eq_single Finset.univ]
  · rw [Finset.piecewise_univ, tensorPowerBasis_apply]
  · intro S _ hS
    obtain ⟨ℓ₀, hℓ₀⟩ : ∃ ℓ, ℓ ∉ S := by
      by_contra hall
      push Not at hall
      exact hS (Finset.eq_univ_of_forall hall)
    have hx0 : S.piecewise m m' ℓ₀ = m' ℓ₀ := Finset.piecewise_eq_of_notMem _ _ _ hℓ₀
    by_cases hb : r ℓ₀ = b
    · have hmem0 : ((rowIndex t ℓ₀, colIndex t ℓ₀) : ℕ × ℕ) ∈ μ := (t.symm ℓ₀).2
      have hrow0 : rowIndex t ℓ₀ = b := congrArg Fin.val hb
      have hcell : ((a : ℕ), colIndex t ℓ₀) ∈ μ :=
        μ.up_left_mem (by rw [hrow0]; exact hab.le) le_rfl hmem0
      set ℓ₁ := t ⟨((a : ℕ), colIndex t ℓ₀), hcell⟩ with hℓ₁_def
      have hr1 : r ℓ₁ = a := Fin.ext (rowIndex_apply t ⟨((a : ℕ), colIndex t ℓ₀), hcell⟩)
      have hcol : colIndex t ℓ₀ = colIndex t ℓ₁ :=
        (colIndex_apply t ⟨((a : ℕ), colIndex t ℓ₀), hcell⟩).symm
      have hne : ℓ₀ ≠ ℓ₁ := fun h => by
        rw [h, hr1] at hb
        exact hab.ne hb
      by_cases hℓ₁ : ℓ₁ ∈ S
      · have hx1 : S.piecewise m m' ℓ₁ = Pi.single a 1 := by
          rw [Finset.piecewise_eq_of_mem _ _ _ hℓ₁]
          simp only [m, hr1]
        have hx0' : S.piecewise m m' ℓ₀ = s • Pi.single a 1 := by
          rw [hx0]
          simp only [m', hmv, hb, ↓reduceIte]
        have hupd : S.piecewise m m' =
            Function.update (S.piecewise m m') ℓ₀ (s • Pi.single a 1) := by
          rw [← hx0', Function.update_eq_self]
        rw [hupd, MultilinearMap.map_update_smul, map_smul,
          permTensorActionAlgHom_youngSymmetrizerOver_tprod_eq_zero t hcol hne
            (by rw [Function.update_self, Function.update_of_ne hne.symm, hx1]), smul_zero]
      · have h0 : S.piecewise m m' ℓ₁ = 0 := by
          rw [Finset.piecewise_eq_of_notMem _ _ _ hℓ₁]
          simp only [m', hmv, hr1, hab.ne, ↓reduceIte, smul_zero]
        rw [MultilinearMap.map_coord_zero _ ℓ₁ h0, map_zero]
    · have h0 : S.piecewise m m' ℓ₀ = 0 := by
        rw [hx0]
        simp only [m', hmv, hb, ↓reduceIte, smul_zero]
      rw [MultilinearMap.map_coord_zero _ ℓ₀ h0, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Symmetrizer

/-! ### The highest weight vector -/

/-- The row-superstandard tableau of `μ`, which defines the Weyl module of the shape `μ`. -/
abbrev rowTableau (μ : YoungDiagram) : YoungTableau μ :=
  (StandardYoungTableau.rowSuperstandard μ).toTableau

variable {μ : YoungDiagram}

variable (K n) in
/-- The **highest weight vector** `c_t (e_{r(1)} ⊗ ⋯ ⊗ e_{r(d)})` of the Weyl module, where `t` is
the row-superstandard tableau of `μ` and `r ℓ` is the row of the label `ℓ`. -/
def irrepHighestVector (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n) : IrrepSpace K n μ :=
  (⟨permTensorActionAlgHom K n μ.card
      (youngSymmetrizerOver K (rowTableau μ))
      (tensorPowerBasis K n μ.card (rowVector (rowTableau μ) hμ)), by
    rw [weylModuleOfShape_toSubmodule]
    exact LinearMap.mem_range_self _ _⟩ : (weylModuleOfShape K n μ).toSubmodule)

theorem irrepIncl_irrepHighestVector (hμ : μ.colLen 0 ≤ n) :
    irrepIncl K n μ (irrepHighestVector K n μ hμ) =
      permTensorActionAlgHom K n μ.card
        (youngSymmetrizerOver K (rowTableau μ))
        (tensorPowerBasis K n μ.card (rowVector (rowTableau μ) hμ)) :=
  rfl

theorem irrepHighestVector_ne_zero (hμ : μ.colLen 0 ≤ n) : irrepHighestVector K n μ hμ ≠ 0 :=
  fun h => youngSymmetrizerOver_rowVector_ne_zero (K := K) (rowTableau μ)
    hμ (by rw [← irrepIncl_irrepHighestVector, h, map_zero])

/-- The highest weight vector has weight `μ` for the torus. -/
theorem irrepHighestVector_mem_weightSpace (hμ : μ.colLen 0 ≤ n) :
    irrepHighestVector K n μ hμ ∈ weightSpace (irrep K n μ) fun i => (μ.rowLen i : ℤ) := by
  rw [mem_torusWeightSpace]
  intro s
  apply irrepIncl_injective
  rw [map_smul, MonoidHom.comp_apply, irrepIncl_irrep, irrepIncl_irrepHighestVector,
    tensorPowerRep_permTensorActionAlgHom, tensorPowerRep_diagGL_tensorPowerBasis, map_smul,
    prod_rowVector (rowTableau μ) hμ fun i => (s i : K)]
  have hw := weightCharHom_natCast (Finsupp.equivFunOnFinite.symm fun i : Fin n => μ.rowLen i) s
  simp only [Finsupp.coe_equivFunOnFinite_symm] at hw
  rw [hw]

/-- The transvections `1 + sE_ab`, `a < b`, fix the highest weight vector. -/
theorem irrep_lineGL_irrepHighestVector (hμ : μ.colLen 0 ≤ n) {a b : Fin n} (hab : a < b)
    (s : K) (hs : (1 + s • (matUnit a b : Matrix (Fin n) (Fin n) K)).det ≠ 0) :
    irrep K n μ (lineGL (matUnit a b) s hs) (irrepHighestVector K n μ hμ) =
      irrepHighestVector K n μ hμ := by
  apply irrepIncl_injective
  rw [irrepIncl_irrep, irrepIncl_irrepHighestVector, tensorPowerRep_permTensorActionAlgHom,
    youngSymmetrizerOver_tensorPowerRep_lineGL _ hμ hab]

/-- **The highest weight vector of `V(μ)`.** -/
theorem isGlHighestWeightVector_irrepHighestVector (hμ : μ.colLen 0 ≤ n) :
    TauCeti.IsGlHighestWeightVector (fun i : Fin n => (μ.rowLen i : K))
      ((isPolynomialRep_irrep μ).toLieRep (irrepHighestVector K n μ hμ)) := by
  set h := isPolynomialRep_irrep (K := K) (n := n) μ
  refine TauCeti.isGlHighestWeightVector_iff.mpr ⟨fun h0 => irrepHighestVector_ne_zero hμ
    (h.toLieRep.injective (h0.trans (map_zero _).symm)), fun i => ?_, fun a b hab => ?_⟩
  · rw [h.lie_toLieRep, h.lie_apply_of_mem_weightSpace (irrepHighestVector_mem_weightSpace hμ) i,
      map_smul, Int.cast_natCast]
  · rw [h.lie_toLieRep, h.lie_eq_zero_of_forall _ _ fun s hs =>
      irrep_lineGL_irrepHighestVector hμ hab s hs, map_zero]

theorem lieSpan_irrepHighestVector (hμ : μ.colLen 0 ≤ n) :
    LieSubmodule.lieSpan K (Matrix (Fin n) (Fin n) K)
      {(isPolynomialRep_irrep μ).toLieRep (irrepHighestVector K n μ hμ)} = ⊤ := by
  have : IsIrreducible K (Matrix (Fin n) (Fin n) K) (isPolynomialRep_irrep (K := K) μ).LieRep :=
    (isPolynomialRep_irrep μ).isIrreducible_iff.mp (isIrreducible_irrep hμ)
  exact lieSpan_eq_top_of_isIrreducible (K := K) (n := n)
    (isGlHighestWeightVector_irrepHighestVector hμ).ne_zero

/-- **The character of `V(μ)` is the Schur polynomial `s_μ`.** -/
theorem character_irrep (hμ : μ.colLen 0 ≤ n) :
    character (irrep K n μ) = TauCeti.diagramSchurPoly n ℤ μ :=
  (isPolynomialRep_irrep μ).character_eq_diagramSchurPoly hμ
    (isGlHighestWeightVector_irrepHighestVector hμ) (lieSpan_irrepHighestVector hμ)

/-! ### The classification -/

/-- **Classification of the irreducible polynomial representations.** Every irreducible
polynomial representation of `GL_n(K)` is equivalent to `V(μ)` for a Young diagram `μ` with at
most `n` rows. -/
theorem IsPolynomialRep.exists_nonempty_equiv_irrep {W : Type*} [AddCommGroup W] [Module K W]
    {ρ : Representation K (GL (Fin n) K) W} (h : IsPolynomialRep ρ) (hirr : ρ.IsIrreducible) :
    ∃ μ : YoungDiagram, μ.colLen 0 ≤ n ∧ Nonempty (ρ.Equiv (irrep K n μ)) := by
  obtain ⟨μ, hμ, hχ⟩ := h.exists_character_eq_diagramSchurPoly hirr
  exact ⟨μ, hμ, IsPolynomialRep.nonempty_equiv_of_character_eq h (isPolynomialRep_irrep μ) hirr
    (isIrreducible_irrep hμ) (hχ.trans (character_irrep hμ).symm)⟩

/-- Young diagrams with at most `n` rows are determined by their first `n` row lengths. -/
theorem eq_of_rowLen_eq {μ ν : YoungDiagram} (hμ : μ.colLen 0 ≤ n) (hν : ν.colLen 0 ≤ n)
    (h : ∀ i : Fin n, μ.rowLen i = ν.rowLen i) : μ = ν := by
  have : weightOfShape n μ = weightOfShape n ν := Subtype.ext (funext fun i => by
    rw [weightOfShape_apply, weightOfShape_apply, h i])
  rw [← shape_weightOfShape hμ, this, shape_weightOfShape hν]

/-- **`V(μ)` determines `μ`.** -/
theorem irrep_eq_of_nonempty_equiv {μ ν : YoungDiagram} (hμ : μ.colLen 0 ≤ n)
    (hν : ν.colLen 0 ≤ n) (e : Nonempty ((irrep K n μ).Equiv (irrep K n ν))) : μ = ν := by
  obtain ⟨e⟩ := e
  have hχ := character_eq_of_equiv (isPolynomialRep_irrep μ) (isPolynomialRep_irrep ν) e
  have hv : ∀ {κ : YoungDiagram} (hκ : κ.colLen 0 ≤ n), TauCeti.IsGlHighestWeightVector
      (fun i : Fin n => (((κ.rowLen i : ℤ)) : K))
      ((isPolynomialRep_irrep κ).toLieRep (irrepHighestVector K n κ hκ)) := fun hκ => by
    simpa only [Int.cast_natCast] using isGlHighestWeightVector_irrepHighestVector hκ
  have := IsPolynomialRep.highestWeight_eq_of_character_eq _ _ hχ (hv hμ)
    (lieSpan_irrepHighestVector hμ) (hv hν) (lieSpan_irrepHighestVector hν)
  exact eq_of_rowLen_eq hμ hν fun i => by exact_mod_cast congrFun this i

/-- **Schur's lemma** for `V(μ)`. -/
theorem finrank_intertwiningMap_irrep_self (hμ : μ.colLen 0 ≤ n) :
    finrank K ((irrep K n μ).IntertwiningMap (irrep K n μ)) = 1 :=
  (isPolynomialRep_irrep μ).finrank_intertwiningMap_self (isIrreducible_irrep hμ)

/-- There are no nonzero intertwining maps between `V(μ)` and `V(ν)` for `μ ≠ ν`. -/
theorem finrank_intertwiningMap_irrep_of_ne {μ ν : YoungDiagram} (hμ : μ.colLen 0 ≤ n)
    (hν : ν.colLen 0 ≤ n) (hne : μ ≠ ν) :
    finrank K ((irrep K n μ).IntertwiningMap (irrep K n ν)) = 0 := by
  have : (irrep K n μ).IsIrreducible := isIrreducible_irrep hμ
  have : (irrep K n ν).IsIrreducible := isIrreducible_irrep hν
  have : IsEmpty ((irrep K n μ).Equiv (irrep K n ν)) :=
    ⟨fun e => hne (irrep_eq_of_nonempty_equiv hμ hν ⟨e⟩)⟩
  exact Module.finrank_zero_of_subsingleton

end

end GLRep
