import Schubert.GLRep.Rational.Torus

/-!
# Rational representations of a split torus: Laurent coefficients and exactness

Let `T = (Kˣ)^κ` be a split torus over a field `K`. This file complements
`Schubert.GLRep.Rational.Torus` with the facts needed for representations of the Borel subgroup.

* A representation of `T` is rational (`GLRep.IsRationalTorusRep`: some twist by a character is
  polynomial) exactly when its matrix coefficients are Laurent functions, that is, lie in Tau
  Ceti's `TauCeti.laurentFunctions` (`GLRep.isRationalTorusRep_iff_hasCoeffsIn_laurentFunctions`).
  Hence rational representations of `T` are closed under subrepresentations, quotients, products,
  tensor products and twists.
* Weight multiplicities are additive on a subrepresentation and its quotient
  (`GLRep.IsRationalTorusRep.finrank_torusWeightSpace_eq_add`), hence so are Laurent characters
  (`GLRep.IsRationalTorusRep.laurentCharacter_eq_add`).
* Laurent characters are invariant under equivalence (`GLRep.laurentCharacter_eq_of_equiv`),
  additive on products and multiplicative on tensor products (`GLRep.laurentCharacter_prod`,
  `GLRep.laurentCharacter_tprod`).
-/

namespace GLRep

open Module TauCeti

noncomputable section

/-! ### Pulling polynomial functions back into a subalgebra -/

section Pullback

variable {K : Type*} [CommRing K] {G H σ : Type*}

/-- If the coordinates of `φ h` are functions of `h` lying in a subalgebra `A`, then `f ∘ φ` lies
in `A` for every polynomial function `f`. -/
theorem comp_mem_of_forall_coord_mem {c : G → σ → K} {A : Subalgebra K (H → K)} (φ : H → G)
    (hφ : ∀ s, (fun h => c (φ h) s) ∈ A) {f : G → K} (hf : f ∈ coordFunctions K c) :
    f ∘ φ ∈ A := by
  have hle : (coordFunctions K c).map (precompAlgHom (K := K) φ) ≤ A := by
    rw [coordFunctions_eq_adjoin, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    exact hφ s
  exact hle ⟨f, hf, rfl⟩

end Pullback

variable {K : Type*} [Field K] {κ : Type*} [Fintype κ]
variable {W : Type*} [AddCommGroup W] [Module K W] {π : Representation K (κ → Kˣ) W}
variable {V : Type*} [AddCommGroup V] [Module K V] {π' : Representation K (κ → Kˣ) V}

/-! ### Laurent functions on the torus -/

section Laurent

/-- A character of nonnegative weight is a polynomial function on the torus. -/
theorem weightCharHom_mem_coordFunctions {μ : κ → ℤ} (hμ : 0 ≤ μ) :
    ⇑(weightCharHom K μ) ∈ coordFunctions K (torusCoord K κ) := by
  have : ⇑(weightCharHom K μ) = ∏ i, (fun t : κ → Kˣ => torusCoord K κ t i) ^ (μ i).toNat := by
    funext t
    rw [Finset.prod_apply]
    simp only [Pi.pow_apply, torusCoord_apply]
    rw [weightCharHom_apply, weightChar_apply, torusCharacter_def, Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : μ i = ((μ i).toNat : ℤ) := (Int.toNat_of_nonneg (hμ i)).symm
    conv_lhs => rw [hi]
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  rw [this]
  exact prod_mem fun i _ => pow_mem (coord_mem_coordFunctions _ i) _

/-- The polynomial functions on the torus are Laurent functions. -/
theorem coordFunctions_torusCoord_le_laurentFunctions :
    coordFunctions K (torusCoord K κ) ≤ laurentFunctions K κ := by
  classical
  refine coordFunctions_le fun i => ?_
  have : (fun t : κ → Kˣ => torusCoord K κ t i) = ⇑(weightCharHom K (Pi.single i 1)) := by
    funext t
    rw [weightCharHom_single, torusCoord_apply]
  rw [this]
  exact weightCharHom_mem_laurentFunctions K _

theorem weightCharHom_const_mul_mem_of_le {f : (κ → Kˣ) → K} {M N : ℕ} (hMN : M ≤ N)
    (hf : ⇑(weightCharHom K fun _ : κ => (M : ℤ)) * f ∈ coordFunctions K (torusCoord K κ)) :
    ⇑(weightCharHom K fun _ : κ => (N : ℤ)) * f ∈ coordFunctions K (torusCoord K κ) := by
  have h : (fun _ : κ => (N : ℤ)) = (fun _ => ((N - M : ℕ) : ℤ)) + fun _ => (M : ℤ) := by
    funext i
    simp only [Pi.add_apply]
    omega
  rw [h, coe_weightCharHom_add, mul_assoc]
  exact mul_mem (weightCharHom_mem_coordFunctions fun _ => Int.natCast_nonneg _) hf

/-- **Every Laurent function becomes polynomial after multiplication by a power of
`∏ᵢ tᵢ`.** -/
theorem exists_weightCharHom_const_mul_mem {f : (κ → Kˣ) → K} (hf : f ∈ laurentFunctions K κ) :
    ∃ N : ℕ,
      ⇑(weightCharHom K fun _ : κ => (N : ℤ)) * f ∈ coordFunctions K (torusCoord K κ) := by
  rw [mem_laurentFunctions_iff] at hf
  induction hf using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨μ, rfl⟩ := h
    refine ⟨Finset.univ.sup fun i => (μ i).natAbs, ?_⟩
    rw [← coe_weightCharHom_add]
    refine weightCharHom_mem_coordFunctions fun i => ?_
    have : (μ i).natAbs ≤ Finset.univ.sup fun i => (μ i).natAbs :=
      Finset.le_sup (f := fun i => (μ i).natAbs) (Finset.mem_univ i)
    simp only [Pi.add_apply, Pi.zero_apply]
    omega
  | zero => exact ⟨0, by rw [mul_zero]; exact zero_mem _⟩
  | add _ _ _ _ hf hg =>
    obtain ⟨M, hM⟩ := hf
    obtain ⟨N, hN⟩ := hg
    refine ⟨M + N, ?_⟩
    rw [mul_add]
    exact add_mem (weightCharHom_const_mul_mem_of_le (by omega) hM)
      (weightCharHom_const_mul_mem_of_le (by omega) hN)
  | smul a _ _ hf =>
    obtain ⟨N, hN⟩ := hf
    exact ⟨N, by rw [mul_smul_comm]; exact Subalgebra.smul_mem _ hN a⟩

/-- A representation of the torus whose matrix coefficients are Laurent functions is
rational. -/
theorem HasCoeffsIn.isRationalTorusRep_of_laurentFunctions
    (h : HasCoeffsIn (laurentFunctions K κ) π) : IsRationalTorusRep π := by
  classical
  have := h.finiteDimensional
  let b := Module.finBasis K W
  choose N hN using fun i j => exists_weightCharHom_const_mul_mem (h.toMatrix_mem b i j)
  let M : ℕ := Finset.univ.sup fun ij : _ × _ => N ij.1 ij.2
  refine ⟨fun _ => (M : ℤ), (hasCoeffsIn_iff_toMatrix b).mpr fun i j => ?_⟩
  have hle : N i j ≤ M :=
    Finset.le_sup (f := fun ij : _ × _ => N ij.1 ij.2) (Finset.mem_univ (i, j))
  have : (fun t =>
      LinearMap.toMatrix b b (GLRep.scaledRep π (weightChar K fun _ => (M : ℤ)) t) i j) =
      ⇑(weightCharHom K fun _ : κ => (M : ℤ)) * fun t => LinearMap.toMatrix b b (π t) i j := by
    funext t
    simp only [LinearMap.toMatrix_apply, scaledRep_apply, map_smul, Finsupp.smul_apply,
      smul_eq_mul, Pi.mul_apply, weightCharHom_apply]
  rw [this]
  exact weightCharHom_const_mul_mem_of_le hle (hN i j)

/-- The matrix coefficients of a rational representation of the torus are Laurent functions. -/
theorem IsRationalTorusRep.hasCoeffsIn_laurentFunctions (h : IsRationalTorusRep π) :
    HasCoeffsIn (laurentFunctions K κ) π := by
  obtain ⟨ν, hν⟩ := h
  refine ⟨hν.finiteDimensional, fun f w => ?_⟩
  have : (fun t => f (π t w)) =
      ⇑(weightCharHom K (-ν)) * fun t => f (scaledRep π (weightChar K ν) t w) := by
    funext t
    rw [Pi.mul_apply, scaledRep_apply, map_smul, smul_eq_mul, ← mul_assoc, weightCharHom_apply,
      ← Units.val_mul, ← MonoidHom.mul_apply, ← weightChar_add, neg_add_cancel, weightChar_zero,
      MonoidHom.one_apply, Units.val_one, one_mul]
  rw [this]
  exact mul_mem (weightCharHom_mem_laurentFunctions K _)
    (coordFunctions_torusCoord_le_laurentFunctions (hν.coeff_mem f w))

/-- **Rational representations of the torus are those with Laurent matrix coefficients.** -/
theorem isRationalTorusRep_iff_hasCoeffsIn_laurentFunctions :
    IsRationalTorusRep π ↔ HasCoeffsIn (laurentFunctions K κ) π :=
  ⟨IsRationalTorusRep.hasCoeffsIn_laurentFunctions,
    HasCoeffsIn.isRationalTorusRep_of_laurentFunctions⟩

namespace IsRationalTorusRep

theorem of_injective (h : IsRationalTorusRep π) (φ : π'.IntertwiningMap π)
    (hφ : Function.Injective φ) : IsRationalTorusRep π' :=
  (h.hasCoeffsIn_laurentFunctions.of_injective φ hφ).isRationalTorusRep_of_laurentFunctions

theorem of_surjective (h : IsRationalTorusRep π) (φ : π.IntertwiningMap π')
    (hφ : Function.Surjective φ) : IsRationalTorusRep π' :=
  (h.hasCoeffsIn_laurentFunctions.of_surjective φ hφ).isRationalTorusRep_of_laurentFunctions

theorem of_equiv (h : IsRationalTorusRep π) (e : π.Equiv π') : IsRationalTorusRep π' :=
  (h.hasCoeffsIn_laurentFunctions.of_equiv e).isRationalTorusRep_of_laurentFunctions

theorem subrepresentation (h : IsRationalTorusRep π) (U : Subrepresentation π) :
    IsRationalTorusRep U.toRepresentation :=
  (h.hasCoeffsIn_laurentFunctions.subrepresentation U).isRationalTorusRep_of_laurentFunctions

theorem quotient (h : IsRationalTorusRep π) (U : Subrepresentation π) :
    IsRationalTorusRep U.quotient :=
  (h.hasCoeffsIn_laurentFunctions.quotient U).isRationalTorusRep_of_laurentFunctions

theorem prod (h : IsRationalTorusRep π) (h' : IsRationalTorusRep π') :
    IsRationalTorusRep (π.prod π') :=
  (h.hasCoeffsIn_laurentFunctions.prod
    h'.hasCoeffsIn_laurentFunctions).isRationalTorusRep_of_laurentFunctions

theorem tprod (h : IsRationalTorusRep π) (h' : IsRationalTorusRep π') :
    IsRationalTorusRep (π.tprod π') :=
  (h.hasCoeffsIn_laurentFunctions.tprod
    h'.hasCoeffsIn_laurentFunctions).isRationalTorusRep_of_laurentFunctions

theorem scaledRep_weightChar (h : IsRationalTorusRep π) (ν : κ → ℤ) :
    IsRationalTorusRep (GLRep.scaledRep π (weightChar K ν)) :=
  (h.hasCoeffsIn_laurentFunctions.scaledRep
    (weightCharHom_mem_laurentFunctions K ν)).isRationalTorusRep_of_laurentFunctions

end IsRationalTorusRep

end Laurent

/-! ### Equivalences -/

section Equiv

/-- An equivalence of representations of the torus maps each weight space onto the weight space of
the same weight. -/
theorem map_torusWeightSpace_equiv (e : π.Equiv π') (μ : κ → ℤ) :
    (torusWeightSpace π μ).map e.toLinearEquiv.toLinearMap = torusWeightSpace π' μ := by
  ext v
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact map_mem_torusWeightSpace e.toIntertwiningMap hw
  · intro hv
    refine ⟨e.symm v, map_mem_torusWeightSpace e.symm.toIntertwiningMap hv, ?_⟩
    exact e.apply_symm_apply v

/-- Equivalent representations of the torus have weight spaces of the same dimension. -/
theorem finrank_torusWeightSpace_eq_of_equiv (e : π.Equiv π') (μ : κ → ℤ) :
    finrank K (torusWeightSpace π μ) = finrank K (torusWeightSpace π' μ) :=
  (e.toLinearEquiv.ofSubmodules _ _ (map_torusWeightSpace_equiv e μ)).finrank_eq

/-- **Equivalent representations of the torus have the same Laurent character.** -/
theorem laurentCharacter_eq_of_equiv (e : π.Equiv π') :
    laurentCharacter π = laurentCharacter π' := by
  have hdim : weightDim K π = weightDim K π' :=
    funext fun μ => by rw [weightDim, weightDim, finrank_torusWeightSpace_eq_of_equiv e μ]
  rw [laurentCharacter, laurentCharacter, hdim]

end Equiv

/-! ### Subrepresentations and quotients -/

section Exact

/-- The weight space of a subrepresentation, as a subspace of the ambient space, is the
intersection of the subrepresentation with the ambient weight space. -/
theorem map_subtype_torusWeightSpace (U : Subrepresentation π) (μ : κ → ℤ) :
    (torusWeightSpace U.toRepresentation μ).map U.toSubmodule.subtype =
      torusWeightSpace π μ ⊓ U.toSubmodule := by
  ext w
  simp only [Submodule.mem_map, Submodule.mem_inf, mem_torusWeightSpace, Submodule.subtype_apply]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun t => congrArg Subtype.val (hu t), u.2⟩
  · rintro ⟨hw, hU⟩
    exact ⟨⟨w, hU⟩, fun t => Subtype.ext (hw t), rfl⟩

/-- The weight spaces of a subrepresentation have the dimensions of the intersections with the
ambient weight spaces. -/
theorem finrank_torusWeightSpace_subrepresentation (U : Subrepresentation π) (μ : κ → ℤ) :
    finrank K (torusWeightSpace U.toRepresentation μ) =
      finrank K ↥(torusWeightSpace π μ ⊓ U.toSubmodule) := by
  rw [← map_subtype_torusWeightSpace]
  exact (Submodule.equivMapOfInjective _ U.toSubmodule.injective_subtype _).finrank_eq

variable [Infinite K]

/-- **Weight multiplicities are additive on a subrepresentation and its quotient.** -/
theorem IsRationalTorusRep.finrank_torusWeightSpace_eq_add (h : IsRationalTorusRep π)
    (U : Subrepresentation π) (μ : κ → ℤ) :
    finrank K (torusWeightSpace π μ) =
      finrank K (torusWeightSpace U.toRepresentation μ) +
        finrank K (torusWeightSpace U.quotient μ) := by
  have := h.finiteDimensional
  let q : π.IntertwiningMap U.quotient := ⟨U.toSubmodule.mkQ, fun _ => rfl⟩
  -- the projection of the weight space of `π` to the weight space of the quotient
  let φ : torusWeightSpace π μ →ₗ[K] torusWeightSpace U.quotient μ :=
    (U.toSubmodule.mkQ.comp (torusWeightSpace π μ).subtype).codRestrict _ fun w =>
      map_mem_torusWeightSpace q w.2
  have hsurj : Function.Surjective φ := by
    classical
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := U.toSubmodule.mkQ_surjective y
    have hx : x ∈ ⨆ ν, torusWeightSpace π ν := by
      rw [h.iSup_torusWeightSpace_eq_top]
      exact Submodule.mem_top
    obtain ⟨f, hf, hfx⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ x).mp hx
    refine ⟨⟨f μ, hf μ⟩, Subtype.ext ?_⟩
    -- `mkQ x - mkQ (f μ)` is a weight vector of weight `μ` in the span of the other weights
    have hd₁ : U.toSubmodule.mkQ x - U.toSubmodule.mkQ (f μ) ∈ torusWeightSpace U.quotient μ :=
      sub_mem hy (map_mem_torusWeightSpace q (hf μ))
    have hterm : ∀ ν ∈ f.support.erase μ, U.toSubmodule.mkQ (f ν) ∈
        ⨆ (ν') (_ : ν' ≠ μ), torusWeightSpace U.quotient ν' := fun ν hν =>
      Submodule.mem_iSup_of_mem ν (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hν)
        (map_mem_torusWeightSpace q (hf ν)))
    have hd₂ : U.toSubmodule.mkQ x - U.toSubmodule.mkQ (f μ) ∈
        ⨆ (ν') (_ : ν' ≠ μ), torusWeightSpace U.quotient ν' := by
      rw [← hfx, Finsupp.sum, map_sum]
      by_cases hμ : μ ∈ f.support
      · rw [← Finset.add_sum_erase _ _ hμ, add_sub_cancel_left]
        exact Submodule.sum_mem _ hterm
      · rw [Finsupp.notMem_support_iff.mp hμ, map_zero, sub_zero, ← Finset.erase_eq_of_notMem hμ]
        exact Submodule.sum_mem _ hterm
    have hdisj := (iSupIndep_def.mp (iSupIndep_torusWeightSpace U.quotient)) μ
    have h0 := Submodule.disjoint_def.mp hdisj _ hd₁ hd₂
    exact (sub_eq_zero.mp h0).symm
  have hker : (LinearMap.ker φ).map (torusWeightSpace π μ).subtype =
      torusWeightSpace π μ ⊓ U.toSubmodule := by
    ext w
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf, Submodule.subtype_apply]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have h0 : U.toSubmodule.mkQ (v : W) = 0 := congrArg Subtype.val hv
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
      exact ⟨v.2, h0⟩
    · rintro ⟨hw, hU⟩
      refine ⟨⟨w, hw⟩, Subtype.ext ?_, rfl⟩
      change U.toSubmodule.mkQ w = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hU
  have hkerdim :
      finrank K (LinearMap.ker φ) = finrank K (torusWeightSpace U.toRepresentation μ) := by
    rw [finrank_torusWeightSpace_subrepresentation, ← hker]
    exact (Submodule.equivMapOfInjective _ (torusWeightSpace π μ).injective_subtype _).finrank_eq
  rw [← LinearMap.finrank_range_add_finrank_ker φ, LinearMap.range_eq_top.mpr hsurj, finrank_top,
    hkerdim, add_comm]

/-- **Laurent characters are additive on a subrepresentation and its quotient.** -/
theorem IsRationalTorusRep.laurentCharacter_eq_add (h : IsRationalTorusRep π)
    (U : Subrepresentation π) :
    laurentCharacter π = laurentCharacter U.toRepresentation + laurentCharacter U.quotient := by
  have := h.finiteDimensional
  refine TorusLaurent.ext fun μ => ?_
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_laurentCharacter, coeff_laurentCharacter,
    coeff_laurentCharacter, h.finrank_torusWeightSpace_eq_add U μ, Nat.cast_add]

end Exact

/-! ### Weight bases -/

section WeightBasis

variable [Infinite K] {ι : Type*} (b : Module.Basis ι K W) (wt : ι → κ → ℤ)

/-- **The weight spaces of a representation with a basis of weight vectors** are spanned by the
basis vectors of the given weight. -/
theorem torusWeightSpace_eq_span_of_basis
    (hb : ∀ t i, π t (b i) = weightCharHom K (wt i) t • b i) (μ : κ → ℤ) :
    torusWeightSpace π μ = Submodule.span K (b '' {i | wt i = μ}) := by
  refine le_antisymm (fun x hx => ?_) ?_
  · rw [b.mem_span_image]
    intro i hi
    by_contra hne
    apply Finsupp.mem_support_iff.mp hi
    have hcoeff : ∀ t : κ → Kˣ,
        b.repr x i * weightCharHom K (wt i) t = weightCharHom K μ t * b.repr x i := by
      intro t
      have h1 := congrArg (fun y => b.repr y i) (apply_of_mem_torusWeightSpace hx t)
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
      rw [← h1]
      conv_rhs => rw [← b.linearCombination_repr x]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_sum, Finset.sum_apply']
      simp only [map_smul, hb, Finsupp.smul_apply, b.repr_self, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · intro hi'
        rw [Finsupp.notMem_support_iff.mp hi', zero_mul]
    by_contra hx0
    apply hne
    refine weightCharHom_injective K (DFunLike.coe_injective (funext fun t => ?_))
    have := hcoeff t
    rw [mul_comm (weightCharHom K μ t)] at this
    exact mul_left_cancel₀ hx0 this
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact mem_torusWeightSpace.mpr fun t => by rw [hb, show wt i = μ from hi]

/-- With a basis of weight vectors, `dim W_μ` is the number of basis vectors of weight `μ`. -/
theorem finrank_torusWeightSpace_of_basis [Fintype ι]
    (hb : ∀ t i, π t (b i) = weightCharHom K (wt i) t • b i) (μ : κ → ℤ) :
    finrank K (torusWeightSpace π μ) = Fintype.card {i // wt i = μ} := by
  rw [torusWeightSpace_eq_span_of_basis b wt hb μ]
  have hrange : b '' {i | wt i = μ} = Set.range (b ∘ (Subtype.val : {i // wt i = μ} → ι)) := by
    ext x
    simp [Set.mem_image, Set.mem_range]
  rw [hrange]
  exact finrank_span_eq_card (b.linearIndependent.comp _ Subtype.val_injective)

/-- **The Laurent character of a representation with a basis of weight vectors** is the sum of
the monomials of the weights of the basis vectors. -/
theorem laurentCharacter_eq_sum_of_basis [Fintype ι]
    (hb : ∀ t i, π t (b i) = weightCharHom K (wt i) t • b i) :
    laurentCharacter π = ∑ i, AddMonoidAlgebra.single (wt i) 1 := by
  classical
  have : FiniteDimensional K W := Module.Finite.of_basis b
  refine TorusLaurent.ext fun μ => ?_
  rw [coeff_laurentCharacter, finrank_torusWeightSpace_of_basis b wt hb μ,
    AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_boole, Fintype.card_subtype]

end WeightBasis

/-! ### Products and tensor products -/

section Products

variable [Infinite K] [CharZero K]

/-- The Laurent character of a product is the sum of the Laurent characters. -/
theorem laurentCharacter_prod (h : IsRationalTorusRep π) (h' : IsRationalTorusRep π') :
    laurentCharacter (π.prod π') = laurentCharacter π + laurentCharacter π' := by
  have := h.finiteDimensional
  have := h'.finiteDimensional
  refine ((h.prod h').eq_laurentCharacter_of_forall _ fun t => ?_).symm
  rw [map_add, ← h.trace_eq_laurentEval, ← h'.trace_eq_laurentEval]
  exact (LinearMap.trace_prodMap' (π t) (π' t)).symm

/-- The Laurent character of a tensor product is the product of the Laurent characters. -/
theorem laurentCharacter_tprod (h : IsRationalTorusRep π) (h' : IsRationalTorusRep π') :
    laurentCharacter (π.tprod π') = laurentCharacter π * laurentCharacter π' := by
  have := h.finiteDimensional
  have := h'.finiteDimensional
  refine ((h.tprod h').eq_laurentCharacter_of_forall _ fun t => ?_).symm
  rw [map_mul, ← h.trace_eq_laurentEval, ← h'.trace_eq_laurentEval, Representation.tprod_apply,
    LinearMap.trace_tensorProduct']

end Products

end

end GLRep
