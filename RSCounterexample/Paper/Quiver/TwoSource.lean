import RSCounterexample.Paper.Quiver.Extraction
import RSCounterexample.Paper.Quiver.Schur.Young

/-!
# The two-source formula

Proposition 5.8 of the paper (`prop:quiver-two-source`). For `n = m + 2` and the interval partition
`{0, 1}, {2}, …, {m + 1}` (0-based), if the comparison weights follow the star pattern (5.9) and
`ν = c − a − b = (ν₁, ν₂, −r₁, …, −r_m)` with `0 ≤ ν₁ ≤ ν₂`, then `(a, b, c)` is a quiver triple for
this partition and

`[𝒜_c](κ_a κ_b) = [s_{(ν₂, ν₁)}] ∏_j h_{r_j}(x₁, x₂)`   (5.10),

the number of semistandard tableaux of shape `(ν₂, ν₁)` and content `r`. It is positive exactly when
`max_j r_j ≤ ν₂` (5.11).

## Main definitions

* `Schubert.RS.Quiver.twoSourcePartition`: the partition `{0, 1}, {2}, …, {m + 1}`.
* `Schubert.RS.Quiver.starPattern`: the comparison weights (5.9).
* `Schubert.RS.Quiver.twoRow`: the two-row shape `(ν₂, ν₁)`.

## Main results

* `Schubert.RS.Quiver.twoSource_isQuiverPartition`.
* `Schubert.RS.Quiver.twoSource_eq_weylProjector`: (5.10).
* `Schubert.RS.Quiver.twoSource_eq_kostka`: the tableau count.
* `Schubert.RS.Quiver.twoSource_pos_iff`: (5.11).
-/

namespace Schubert.RS.Quiver

noncomputable section

open MvPolynomial Representation

/-! ## The partition `{0, 1}, {2}, …, {m + 1}` -/

/-- The interval partition `{0, 1}, {2}, …, {m + 1}` of `{0, …, m + 1}`. -/
def twoSourcePartition (m : ℕ) : IntervalPartition (m + 2) where
  blocks := 2 :: List.replicate m 1
  blocks_pos := by
    intro i hi
    simp only [List.mem_cons, List.mem_replicate] at hi
    omega
  blocks_sum := by simp [add_comm]

variable {m : ℕ}

theorem twoSourcePartition_length : (twoSourcePartition m).length = m + 1 := by
  change (2 :: List.replicate m 1).length = m + 1
  simp

/-- The block `{0, 1}`. -/
def twoSourceBlock (m : ℕ) : Fin (twoSourcePartition m).length :=
  ⟨0, by rw [twoSourcePartition_length]; omega⟩

/-- The singleton block `{j + 2}`. -/
def singletonBlock (j : Fin m) : Fin (twoSourcePartition m).length :=
  ⟨j.val + 1, by rw [twoSourcePartition_length]; omega⟩

theorem blocksFun_twoSourceBlock : (twoSourcePartition m).blocksFun (twoSourceBlock m) = 2 := rfl

theorem twoSourceBlock_val : (twoSourceBlock m : ℕ) = 0 := rfl

theorem singletonBlock_val (j : Fin m) : (singletonBlock j : ℕ) = j.val + 1 := rfl

theorem blocksFun_singletonBlock (j : Fin m) :
    (twoSourcePartition m).blocksFun (singletonBlock j) = 1 := by
  simp [_root_.Composition.blocksFun, twoSourcePartition, singletonBlock]

theorem sizeUpTo_twoSource {k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m + 1) :
    (twoSourcePartition m).sizeUpTo k = k + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [_root_.Composition.sizeUpTo, twoSourcePartition, List.take_succ_cons,
    List.sum_cons, List.take_replicate, List.sum_replicate, smul_eq_mul, mul_one]
  omega

theorem embedding_twoSourceBlock
    (k : Fin ((twoSourcePartition m).blocksFun (twoSourceBlock m))) :
    ((twoSourcePartition m).embedding (twoSourceBlock m) k : ℕ) = k := by
  rw [_root_.Composition.coe_embedding, twoSourceBlock_val, _root_.Composition.sizeUpTo_zero,
    zero_add]

theorem embedding_singletonBlock (j : Fin m) (k : Fin ((twoSourcePartition m).blocksFun
    (singletonBlock j))) :
    ((twoSourcePartition m).embedding (singletonBlock j) k : ℕ) = j.val + 2 := by
  rw [_root_.Composition.coe_embedding, singletonBlock_val]
  have hk : k.val = 0 := by
    have h1 := k.isLt
    have h2 := blocksFun_singletonBlock j
    omega
  rw [sizeUpTo_twoSource (by omega) (by omega), hk]

theorem index_twoSource_of_lt {i : Fin (m + 2)} (hi : i.val < 2) :
    (twoSourcePartition m).index i = twoSourceBlock m := by
  have h : i = (twoSourcePartition m).embedding (twoSourceBlock m)
      ⟨i.val, by rw [blocksFun_twoSourceBlock]; exact hi⟩ := by
    ext
    rw [embedding_twoSourceBlock]
  exact (congrArg (twoSourcePartition m).index h).trans
    (_root_.Composition.index_embedding _ _ _)

theorem index_twoSource_of_le {i : Fin (m + 2)} (hi : 2 ≤ i.val) :
    (twoSourcePartition m).index i = singletonBlock ⟨i.val - 2, by omega⟩ := by
  have h1 : 0 < (twoSourcePartition m).blocksFun (singletonBlock ⟨i.val - 2, by omega⟩) := by
    rw [blocksFun_singletonBlock]
    exact Nat.one_pos
  have h : i = (twoSourcePartition m).embedding (singletonBlock ⟨i.val - 2, by omega⟩)
      ⟨0, h1⟩ := by
    ext
    rw [embedding_singletonBlock]
    simp only
    omega
  exact (congrArg (twoSourcePartition m).index h).trans
    (_root_.Composition.index_embedding _ _ _)

theorem index_twoSource_val (i : Fin (m + 2)) :
    ((twoSourcePartition m).index i : ℕ) = i.val - 1 := by
  rcases Nat.lt_or_ge i.val 2 with hi | hi
  · rw [index_twoSource_of_lt hi]
    simp only [twoSourceBlock]
    omega
  · rw [index_twoSource_of_le hi]
    simp only [singletonBlock]
    omega

/-! ## The star pattern -/

/-- The comparison weights (5.9), 0-based: `−1` for the pair `(0, 1)`, `1` from `{0, 1}` to the
other positions, and `0` among the other positions. -/
def starPattern (i j : ℕ) : ℤ := if j = 1 then -1 else if i ≤ 1 then 1 else 0

theorem cmp_eq_neg_one_iff (P R : ℕ × ℕ × ℕ) :
    Window.cmp P R = -1 ↔ R.1 ≤ P.1 ∧ R.2.1 ≤ P.2.1 ∧ R.2.2 ≤ P.2.2 := by
  unfold Window.cmp
  split_ifs <;> omega

section Partition

variable {a b c : Composition (m + 2)} {N : ℕ}

/-- **The two-source partition is a quiver partition** (the first claim of Proposition 5.8). -/
theorem twoSource_isQuiverPartition (hW : Window.Hypotheses a b c N)
    (hstar : ∀ i j : Fin (m + 2), i < j →
      Window.cmp (Window.triple a b (Window.complement N c) i)
        (Window.triple a b (Window.complement N c) j) = starPattern i j) :
    IsQuiverPartition a b c N (twoSourcePartition m) := by
  refine ⟨hW, fun i j hij hidx => ?_, fun p q hpq => ?_⟩
  · rcases eq_or_lt_of_le hij with h | h
    · subst h
      exact ⟨le_rfl, le_rfl, le_rfl⟩
    · have hi := index_twoSource_val i
      have hj := index_twoSource_val j
      rw [hidx] at hi
      have hlt : i.val < j.val := h
      have hi0 : i.val = 0 := by omega
      have hj1 : j.val = 1 := by omega
      have hc := hstar i j h
      rw [starPattern, ite_eq_left hj1, cmp_eq_neg_one_iff] at hc
      exact hc
  · by_cases hp : p.val = 0
    · refine ⟨1, fun i j hi hj => ?_⟩
      have hiv := index_twoSource_val i
      have hjv := index_twoSource_val j
      rw [hi] at hiv
      rw [hj] at hjv
      have hq : 0 < q.val := by have := Fin.lt_def.mp hpq; omega
      have hij : i < j := Fin.lt_def.mpr (by omega)
      rw [hstar i j hij, starPattern, ite_eq_right (by omega), ite_eq_left (by omega)]
      rfl
    · refine ⟨0, fun i j hi hj => ?_⟩
      have hiv := index_twoSource_val i
      have hjv := index_twoSource_val j
      rw [hi] at hiv
      rw [hj] at hjv
      have hpq' : p.val < q.val := hpq
      have hij : i < j := Fin.lt_def.mpr (by omega)
      rw [hstar i j hij, starPattern, ite_eq_right (by omega), ite_eq_right (by omega)]
      rfl

end Partition

/-! ## The first two variables inside `Laurent (m + 2)` -/

/-- Extending a weight of the first two variables by zero. -/
def extendTwo (m : ℕ) : Weight 2 →+ Weight (m + 2) where
  toFun w i := if h : i.val < 2 then w ⟨i.val, h⟩ else 0
  map_zero' := by
    funext i
    simp
  map_add' v w := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp

theorem extendTwo_apply_castLE (w : Weight 2) (k : Fin 2) :
    extendTwo m w (Fin.castLE (by omega) k) = w k := by
  simp only [extendTwo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.val_castLE]
  split_ifs with h
  · rfl
  · exact absurd k.isLt h

theorem extendTwo_injective : Function.Injective (extendTwo m) := fun v w h => by
  funext k
  have := congrFun h (Fin.castLE (by omega) k)
  rwa [extendTwo_apply_castLE, extendTwo_apply_castLE] at this

theorem extendTwo_single_apply (k : Fin 2) (z : ℤ) (i : Fin (m + 2)) :
    extendTwo m (Pi.single k z) i = if i.val = k.val then z else 0 := by
  have hk := k.isLt
  simp only [extendTwo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/-- The Laurent polynomials in the first two variables inside `Laurent (m + 2)`. -/
def embedTwo (m : ℕ) : Laurent 2 →+* Laurent (m + 2) :=
  AddMonoidAlgebra.mapDomainRingHom ℤ (extendTwo m)

theorem embedTwo_single (w : Weight 2) (z : ℤ) :
    embedTwo m (AddMonoidAlgebra.single w z) = AddMonoidAlgebra.single (extendTwo m w) z :=
  AddMonoidAlgebra.mapDomain_single

/-- The coefficients of a Laurent polynomial in the first two variables. -/
theorem coeff_embedTwo (G : Laurent 2) (v : Weight (m + 2)) :
    (embedTwo m G).coeff v = if ∀ i : Fin (m + 2), 2 ≤ i.val → v i = 0 then
      G.coeff (fun k => v (Fin.castLE (by omega) k)) else 0 := by
  change Finsupp.mapDomain (extendTwo m) (AddMonoidAlgebra.coeff G) v = _
  split_ifs with hv
  · have hv' : v = extendTwo m (fun k => v (Fin.castLE (by omega) k)) := by
      funext i
      simp only [extendTwo, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      split_ifs with h
      · rfl
      · exact hv i (by omega)
    conv_lhs => rw [hv']
    exact Finsupp.mapDomain_apply_of_injective extendTwo_injective _ _
  · apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨w, rfl⟩
    apply hv
    intro i hi
    simp only [extendTwo, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    split_ifs with h
    · omega
    · rfl

theorem embedTwo_weylFactor :
    embedTwo m (Schubert.RS.weylFactor 2) =
      1 - AddMonoidAlgebra.single (positiveRoot (0 : Fin (m + 2)) 1) 1 := by
  rw [Schubert.RS.weylFactor, Fin.prod_univ_two]
  have h0 : (Finset.univ.filter fun l : Fin 2 => (0 : Fin 2) < l) = {1} := by decide
  have h1 : (Finset.univ.filter fun l : Fin 2 => (1 : Fin 2) < l) = ∅ := by decide
  rw [h0, h1, Finset.prod_singleton, Finset.prod_empty, mul_one, map_sub, map_one,
    embedTwo_single]
  congr 2
  funext i
  simp only [positiveRoot, map_sub, Pi.sub_apply, extendTwo_single_apply, Pi.single_apply,
    Fin.ext_iff]
  simp

/-- `h_ℓ` of `y_k z` is `z^ℓ h_ℓ(y)`. -/
theorem aeval_hsymm_mul_const {K A : Type*} [Fintype K] [DecidableEq K] [CommRing A]
    [Algebra ℤ A] (g : K → A) (z : A) (ℓ : ℕ) :
    aeval (fun k => g k * z) (hsymm K ℤ ℓ) = z ^ ℓ * aeval g (hsymm K ℤ ℓ) := by
  simp only [hsymm, map_sum, Finset.mul_sum, map_multiset_prod, Multiset.map_map,
    Function.comp_def, aeval_X]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, s.2, mul_comm]

/-! ## The quiver of the two-source partition -/

section Quiver

variable {a b c : Composition (m + 2)} {N : ℕ}

theorem first_twoSource_val (p : Fin (twoSourcePartition m).length) :
    ((twoSourcePartition m).first p : ℕ) = if p.val = 0 then 0 else p.val + 1 := by
  rw [IntervalPartition.first, _root_.Composition.coe_embedding]
  have hp := p.isLt
  have hl := twoSourcePartition_length (m := m)
  split_ifs with h
  · rw [h, _root_.Composition.sizeUpTo_zero]
    rfl
  · rw [sizeUpTo_twoSource (by omega) (by omega)]
    rfl

theorem twoSource_arrows
    (hstar : ∀ i j : Fin (m + 2), i < j →
      Window.cmp (Window.triple a b (Window.complement N c) i)
        (Window.triple a b (Window.complement N c) j) = starPattern i j)
    (p q : Fin (twoSourcePartition m).length) :
    (if p < q then (Window.cmp
        (Window.triple a b (Window.complement N c) ((twoSourcePartition m).first p))
        (Window.triple a b (Window.complement N c) ((twoSourcePartition m).first q))).toNat
      else 0) = if p.val = 0 ∧ 0 < q.val then 1 else 0 := by
  by_cases hpq : p < q
  · rw [ite_eq_left hpq]
    have hlt : (twoSourcePartition m).first p < (twoSourcePartition m).first q :=
      (twoSourcePartition m).embedding_lt_embedding hpq _ _
    rw [hstar _ _ hlt, starPattern, first_twoSource_val, first_twoSource_val]
    have hq : q.val ≠ 0 := by have := Fin.lt_def.mp hpq; omega
    by_cases hp : p.val = 0
    · simp [hp, hq, Nat.pos_of_ne_zero hq]
    · have := Fin.lt_def.mp hpq
      simp [hp, hq]
  · rw [ite_eq_right hpq]
    have : ¬ (p.val = 0 ∧ 0 < q.val) := fun h => hpq (Fin.lt_def.mpr (by omega))
    simp [this]

/-- The relabelling of the blocks by `Fin (m + 1)`. -/
def blockIndex (m : ℕ) : Fin (m + 1) ≃ Fin (twoSourcePartition m).length :=
  finCongr twoSourcePartition_length.symm

theorem blockIndex_zero : blockIndex m 0 = twoSourceBlock m := rfl

theorem blockIndex_succ (j : Fin m) : blockIndex m j.succ = singletonBlock j := rfl

theorem prod_blocks {M : Type*} [CommMonoid M] (F : Fin (twoSourcePartition m).length → M) :
    ∏ p, F p = F (twoSourceBlock m) * ∏ j : Fin m, F (singletonBlock j) := by
  rw [← Equiv.prod_comp (blockIndex m), Fin.prod_univ_succ]
  rfl

/-- A product over the arrows of the two-source quiver: one arrow from `{0, 1}` to every singleton
block. -/
theorem prod_arrow_twoSource
    (hstar : ∀ i j : Fin (m + 2), i < j →
      Window.cmp (Window.triple a b (Window.complement N c) i)
        (Window.triple a b (Window.complement N c) j) = starPattern i j)
    {M : Type*} [CommMonoid M] (F : Fin (twoSourcePartition m).length →
      Fin (twoSourcePartition m).length → M) :
    ∏ e : (quiverOf a b c N (twoSourcePartition m)).Arrow,
        F ((quiverOf a b c N (twoSourcePartition m)).src e)
          ((quiverOf a b c N (twoSourcePartition m)).tgt e) =
      ∏ j : Fin m, F (twoSourceBlock m) (singletonBlock j) := by
  rw [ForwardQuiver.prod_arrow (quiverOf a b c N (twoSourcePartition m)) F]
  simp only [twoSource_arrows hstar]
  simp [prod_blocks, twoSourceBlock_val, singletonBlock_val]

theorem weylPoly_twoSource :
    weylPoly (twoSourcePartition m) =
      1 - MvPolynomial.monomial (rootDegree (0 : Fin (m + 2)) 1) 1 := by
  rw [weylPoly, prod_blocks]
  have hsing : ∀ j : Fin m, ∏ k : Fin ((twoSourcePartition m).blocksFun (singletonBlock j)),
      ∏ l ∈ Finset.univ.filter (k < ·), (1 - MvPolynomial.monomial
        (rootDegree ((twoSourcePartition m).embedding (singletonBlock j) k)
          ((twoSourcePartition m).embedding (singletonBlock j) l)) (1 : ℤ)) = 1 := by
    intro j
    refine Finset.prod_eq_one fun k _ => Finset.prod_eq_one fun l hl => ?_
    have hkl := Fin.lt_def.mp (Finset.mem_filter.mp hl).2
    have h1 := l.isLt
    have h2 := blocksFun_singletonBlock j
    omega
  rw [Finset.prod_eq_one fun j _ => hsing j, mul_one]
  change ∏ k : Fin 2, ∏ l ∈ Finset.univ.filter (fun l : Fin 2 => k < l), (1 - MvPolynomial.monomial
    (rootDegree ((twoSourcePartition m).embedding (twoSourceBlock m) k)
      ((twoSourcePartition m).embedding (twoSourceBlock m) l)) (1 : ℤ)) = _
  rw [Fin.prod_univ_two]
  have h0 : (Finset.univ.filter fun l : Fin 2 => (0 : Fin 2) < l) = {1} := by decide
  have h1 : (Finset.univ.filter fun l : Fin 2 => (1 : Fin 2) < l) = ∅ := by decide
  rw [h0, h1, Finset.prod_singleton, Finset.prod_empty, mul_one]
  have e0 : (twoSourcePartition m).embedding (twoSourceBlock m)
      (show Fin ((twoSourcePartition m).blocksFun (twoSourceBlock m)) from (0 : Fin 2)) = 0 := by
    ext
    rw [embedding_twoSourceBlock]
    rfl
  have e1 : (twoSourcePartition m).embedding (twoSourceBlock m)
      (show Fin ((twoSourcePartition m).blocksFun (twoSourceBlock m)) from (1 : Fin 2)) = 1 := by
    ext
    rw [embedding_twoSourceBlock]
    rfl
  rw [e0, e1]

/-- The position `j + 2` of the singleton block `{j + 2}`. -/
def singletonPos (j : Fin m) : Fin (m + 2) := ⟨j.val + 2, by omega⟩

theorem embedding_singletonBlock_eq (j : Fin m)
    (k : Fin ((twoSourcePartition m).blocksFun (singletonBlock j))) :
    (twoSourcePartition m).embedding (singletonBlock j) k = singletonPos j :=
  Fin.ext (embedding_singletonBlock j k)

theorem embedding_twoSourceBlock_eq
    (k : Fin ((twoSourcePartition m).blocksFun (twoSourceBlock m))) :
    (twoSourcePartition m).embedding (twoSourceBlock m) k =
      ⟨k.val, by have h1 := k.isLt; have h2 := blocksFun_twoSourceBlock (m := m); omega⟩ :=
  Fin.ext (embedding_twoSourceBlock k)

theorem positiveRoot_pair_singleton (k : Fin 2) (j : Fin m) :
    positiveRoot (⟨k.val, by omega⟩ : Fin (m + 2)) (singletonPos j) =
      extendTwo m (Pi.single k 1) + -Pi.single (singletonPos j) (1 : ℤ) := by
  funext i
  simp only [positiveRoot, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, extendTwo_single_apply,
    Pi.single_apply, Fin.ext_iff, singletonPos]
  split_ifs <;> rfl

theorem rootCoordinateEmbedding_arrowPoly_twoSource (B : ℕ) (j : Fin m) :
    rootCoordinateEmbedding (arrowPoly (twoSourcePartition m) B (twoSourceBlock m)
        (singletonBlock j)) =
      ∑ ℓ ∈ Finset.range (B + 1),
        AddMonoidAlgebra.single (ℓ • -Pi.single (singletonPos j) (1 : ℤ)) 1 *
          embedTwo m (toLaurent (hsymm (Fin 2) ℤ ℓ)) := by
  rw [arrowPoly, map_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [map_aeval_int]
  have hmon : ∀ kl : Fin ((twoSourcePartition m).blocksFun (twoSourceBlock m)) ×
      Fin ((twoSourcePartition m).blocksFun (singletonBlock j)),
      rootCoordinateEmbedding (MvPolynomial.monomial (rootDegree
        ((twoSourcePartition m).embedding (twoSourceBlock m) kl.1)
        ((twoSourcePartition m).embedding (singletonBlock j) kl.2)) (1 : ℤ)) =
      embedTwo m (AddMonoidAlgebra.single (Pi.single kl.1 1 : Weight 2) 1) *
        AddMonoidAlgebra.single (-Pi.single (singletonPos j) (1 : ℤ)) 1 := by
    intro kl
    rw [rootCoordinateEmbedding_monomial_rootDegree
      ((twoSourcePartition m).embedding_lt_embedding
        (Fin.lt_def.mpr (by simp [twoSourceBlock_val, singletonBlock_val])) _ _),
      embedding_twoSourceBlock_eq, embedding_singletonBlock_eq, embedTwo_single,
      AddMonoidAlgebra.single_mul_single, mul_one]
    exact congrArg (fun w => AddMonoidAlgebra.single w (1 : ℤ))
      (positiveRoot_pair_singleton kl.1 j)
  simp only [hmon]
  rw [aeval_hsymm_mul_const, AddMonoidAlgebra.single_pow, one_pow]
  congr 1
  have : Unique (Fin ((twoSourcePartition m).blocksFun (singletonBlock j))) :=
    (finCongr (blocksFun_singletonBlock j)).unique
  rw [← rename_hsymm (R := ℤ) (n := ℓ) (e := (Equiv.prodUnique
      (Fin ((twoSourcePartition m).blocksFun (twoSourceBlock m)))
      (Fin ((twoSourcePartition m).blocksFun (singletonBlock j)))).symm),
    aeval_rename]
  simp only [Function.comp_def, Equiv.prodUnique_symm_apply]
  change aeval (fun t : Fin 2 => embedTwo m (AddMonoidAlgebra.single (Pi.single t 1 : Weight 2) 1))
    (hsymm (Fin 2) ℤ ℓ) = _
  simp only [← Schur.toLaurent_X]
  rw [← map_aeval_int, ← map_aeval_int, aeval_X_left_apply]

end Quiver

/-! ## The two-source formula (5.10) -/

/-- The exponent `−∑_j ℓ_j e_{j+2}` of `∏_j x_{j+2}^{−ℓ_j}`. -/
def singletonWeight (ℓ : Fin m → ℕ) : Weight (m + 2) :=
  ∑ j, ℓ j • -Pi.single (singletonPos j) (1 : ℤ)

theorem singletonPos_injective : Function.Injective (singletonPos (m := m)) := fun j j' h => by
  have := congrArg Fin.val h
  simp only [singletonPos] at this
  exact Fin.ext (by omega)

theorem singletonWeight_singletonPos (ℓ : Fin m → ℕ) (j : Fin m) :
    singletonWeight ℓ (singletonPos j) = -(ℓ j : ℤ) := by
  rw [singletonWeight, Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    have hne : singletonPos j ≠ singletonPos j' := singletonPos_injective.ne (Ne.symm hj')
    simp [hne]
  · simp

theorem singletonWeight_of_lt (ℓ : Fin m → ℕ) {i : Fin (m + 2)} (hi : i.val < 2) :
    singletonWeight ℓ i = 0 := by
  rw [singletonWeight, Finset.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hne : i ≠ singletonPos j := fun h => by
    have := congrArg Fin.val h
    simp only [singletonPos] at this
    omega
  simp [hne]

theorem singletonPos_of_le {i : Fin (m + 2)} (hi : 2 ≤ i.val) :
    i = singletonPos ⟨i.val - 2, by omega⟩ := by
  ext
  simp only [singletonPos]
  omega

section Formula

variable {a b c : Composition (m + 2)} {N : ℕ} {ν₁ ν₂ : ℕ} {r : Fin m → ℕ}

/-- **The two-source formula** (5.10): the atom coefficient is the coefficient of `s_{(ν₂, ν₁)}` in
`∏_j h_{r_j}(x₁, x₂)`, written with the Weyl projector (5.7) at `u = (ν₁, ν₂)`. -/
theorem twoSource_eq_weylProjector (hW : Window.Hypotheses a b c N)
    (hstar : ∀ i j : Fin (m + 2), i < j →
      Window.cmp (Window.triple a b (Window.complement N c) i)
        (Window.triple a b (Window.complement N c) j) = starPattern i j)
    (hν₁ : Window.residual a b c 0 = ν₁) (hν₂ : Window.residual a b c 1 = ν₂)
    (hr : ∀ j, Window.residual a b c (singletonPos j) = -(r j : ℤ)) :
    atomCoefficient (key a * key b) c =
      Schur.weylProjector ![(ν₁ : ℤ), ν₂] (toLaurent (∏ j, hsymm (Fin 2) ℤ (r j))) := by
  classical
  have h := twoSource_isQuiverPartition hW hstar
  set B := ∑ i, (Window.residual a b c i).natAbs with hBdef
  have hB : ∀ i, Window.heightDegree a b c i ≤ B := by
    intro i
    have h1 := heightDegree_le_sum_abs (a := a) (b := b) (c := c) i
    have h2 : ((B : ℕ) : ℤ) = ∑ j, |Window.residual a b c j| := by
      simp [hBdef]
    exact_mod_cast h1.trans h2.symm.le
  have hrB : ∀ j, r j ≤ B := by
    intro j
    have h1 := Finset.single_le_sum (fun i _ => Nat.zero_le ((Window.residual a b c i).natAbs))
      (Finset.mem_univ (singletonPos j))
    rw [hr j] at h1
    simpa using h1
  have h01 : (0 : Fin (m + 2)) < 1 := Fin.lt_def.mpr (by simp)
  rw [atomCoefficient_eq_coeff_arrowPoly h B hB,
    prod_arrow_twoSource hstar (fun p q => arrowPoly (twoSourcePartition m) B p q), map_mul,
    map_prod, weylPoly_twoSource, map_sub, map_one,
    rootCoordinateEmbedding_monomial_rootDegree h01, ← embedTwo_weylFactor]
  simp only [rootCoordinateEmbedding_arrowPoly_twoSource]
  rw [Finset.prod_univ_sum, Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finsupp.coe_finsetSum,
    Finset.sum_apply]
  -- each summand
  have hterm : ∀ ℓ : Fin m → ℕ,
      (embedTwo m (Schubert.RS.weylFactor 2) * ∏ j, (AddMonoidAlgebra.single
        (ℓ j • -Pi.single (singletonPos j) (1 : ℤ)) 1 *
          embedTwo m (toLaurent (hsymm (Fin 2) ℤ (ℓ j))))).coeff (Window.residual a b c) =
      if ℓ = r then (Schubert.RS.weylFactor 2 *
        toLaurent (∏ j, hsymm (Fin 2) ℤ (ℓ j))).coeff ![(ν₁ : ℤ), ν₂] else 0 := by
    intro ℓ
    rw [Finset.prod_mul_distrib, AddMonoidAlgebra.prod_single, Finset.prod_const_one, ← map_prod,
      mul_left_comm, ← map_mul, ← singletonWeight, AddMonoidAlgebra.coeff_single_mul_apply,
      one_mul, coeff_embedTwo, ← map_prod]
    by_cases hℓ : ℓ = r
    · subst hℓ
      rw [ite_eq_left rfl, ite_eq_left]
      · congr 1
        funext k
        rw [Pi.add_apply, Pi.neg_apply,
          singletonWeight_of_lt _ (by rw [Fin.val_castLE]; exact k.isLt), neg_zero, zero_add]
        rcases k with ⟨k, hk⟩
        have hk' : k = 0 ∨ k = 1 := by omega
        rcases hk' with rfl | rfl
        · have e : (⟨0, by omega⟩ : Fin (m + 2)) = 0 := Fin.ext (by simp)
          exact (congrArg (Window.residual a b c) e).trans hν₁
        · have e : (⟨1, by omega⟩ : Fin (m + 2)) = 1 := Fin.ext (by simp)
          exact (congrArg (Window.residual a b c) e).trans hν₂
      · intro i hi
        rw [singletonPos_of_le hi, Pi.add_apply, Pi.neg_apply, singletonWeight_singletonPos, hr]
        ring
    · rw [ite_eq_right hℓ, ite_eq_right]
      intro hall
      apply hℓ
      funext j
      have := hall (singletonPos j) (by simp [singletonPos])
      rw [Pi.add_apply, Pi.neg_apply, singletonWeight_singletonPos, hr] at this
      omega
  simp only [hterm]
  rw [Finset.sum_ite_eq']
  rw [ite_eq_left (Fintype.mem_piFinset.mpr fun j => Finset.mem_range.mpr (Nat.lt_succ_of_le
    (hrB j)))]
  rfl

end Formula

/-! ## Two-row shapes -/

section TwoRow

variable {ν₁ ν₂ : ℕ}

/-- The dominant weight `(ν₂, ν₁)` of `GL₂`. -/
def twoRowWeight (h : ν₁ ≤ ν₂) : TauCeti.DominantWeight 2 :=
  ⟨![(ν₂ : ℤ), ν₁], fun i j hij => by
    fin_cases i <;> fin_cases j <;> simp_all⟩

/-- The two-row Young diagram `(ν₂, ν₁)`. -/
def twoRow (h : ν₁ ≤ ν₂) : YoungDiagram := (twoRowWeight h).shape

theorem isPolynomial_twoRowWeight (h : ν₁ ≤ ν₂) : (twoRowWeight h).IsPolynomial := by
  intro i
  fin_cases i <;> simp [twoRowWeight]

theorem twoRow_rowLen_zero (h : ν₁ ≤ ν₂) : (twoRow h).rowLen 0 = ν₂ := by
  have := TauCeti.DominantWeight.rowLen_shape (twoRowWeight h) 0
  simpa [twoRow, twoRowWeight] using this

theorem twoRow_rowLen_one (h : ν₁ ≤ ν₂) : (twoRow h).rowLen 1 = ν₁ := by
  have := TauCeti.DominantWeight.rowLen_shape (twoRowWeight h) 1
  simpa [twoRow, twoRowWeight] using this

theorem mem_twoRow (h : ν₁ ≤ ν₂) {i c : ℕ} :
    (i, c) ∈ twoRow h ↔ (i = 0 ∧ c < ν₂) ∨ (i = 1 ∧ c < ν₁) := by
  rw [YoungDiagram.mem_iff_lt_rowLen]
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i
    · rw [twoRow_rowLen_zero]
      omega
    · rw [twoRow_rowLen_one]
      omega
  · rw [twoRow, TauCeti.DominantWeight.rowLen_shape_eq_zero_of_le _ hi]
    omega

end TwoRow

/-! ## Two-row Kostka numbers -/

section TwoRowKostka

variable (r : Fin m → ℕ)

/-- The prefix sums `r_0 + ⋯ + r_{k−1}`. -/
def prefixSum (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, Schur.contentOf r i

theorem prefixSum_succ (k : ℕ) :
    prefixSum r (k + 1) = prefixSum r k + Schur.contentOf r k := by
  rw [prefixSum, prefixSum, Finset.sum_range_succ]

theorem prefixSum_mono : Monotone (prefixSum r) := fun _ _ hkl =>
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hkl)

theorem prefixSum_m : prefixSum r m = ∑ j, r j := by
  rw [prefixSum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Schur.contentOf, j.isLt]

/-- The letter at position `t` of the sorted word `0^{r_0} 1^{r_1} ⋯`. -/
def label (t : ℕ) : ℕ :=
  Nat.find (p := fun k => t < prefixSum r (k + 1) ∨ m ≤ k) ⟨m, Or.inr le_rfl⟩

theorem label_mono : Monotone (label r) := fun t t' htt' => by
  unfold label
  exact Nat.find_mono fun k hk => hk.imp (lt_of_le_of_lt htt') id

theorem label_spec {t : ℕ} (ht : t < prefixSum r m) :
    label r t < m ∧ prefixSum r (label r t) ≤ t ∧ t < prefixSum r (label r t + 1) := by
  have hm : 0 < m := by
    by_contra h0
    have : m = 0 := by omega
    subst this
    simp [prefixSum] at ht
  have hspec := Nat.find_spec (p := fun k => t < prefixSum r (k + 1) ∨ m ≤ k) ⟨m, Or.inr le_rfl⟩
  have hle : label r t ≤ m - 1 := Nat.find_min' _ (Or.inl (by
    rw [show m - 1 + 1 = m by omega]
    exact ht))
  have hL : label r t < m := by omega
  refine ⟨hL, ?_, hspec.resolve_right (by unfold label at hL; omega)⟩
  rcases Nat.eq_zero_or_pos (label r t) with h0 | hpos
  · rw [h0, prefixSum, Finset.range_zero, Finset.sum_empty]
    exact Nat.zero_le _
  · have hmin := Nat.find_min (p := fun k => t < prefixSum r (k + 1) ∨ m ≤ k)
      ⟨m, Or.inr le_rfl⟩ (m := label r t - 1) (by unfold label at hpos ⊢; omega)
    push Not at hmin
    have := hmin.1
    rwa [show label r t - 1 + 1 = label r t by omega] at this

theorem label_eq_iff {t k : ℕ} (ht : t < prefixSum r m) (hk : k < m) :
    label r t = k ↔ prefixSum r k ≤ t ∧ t < prefixSum r (k + 1) := by
  obtain ⟨hL, h1, h2⟩ := label_spec r ht
  constructor
  · rintro rfl
    exact ⟨h1, h2⟩
  · rintro ⟨h3, h4⟩
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := prefixSum_mono r (show label r t + 1 ≤ k by omega)
      omega
    · have := prefixSum_mono r (show k + 1 ≤ label r t by omega)
      omega

theorem card_label_eq (k : ℕ) :
    ((Finset.range (prefixSum r m)).filter fun t => label r t = k).card =
      Schur.contentOf r k := by
  rcases Nat.lt_or_ge k m with hk | hk
  · have hset : ((Finset.range (prefixSum r m)).filter fun t => label r t = k) =
        Finset.Ico (prefixSum r k) (prefixSum r (k + 1)) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨ht, hlab⟩
        exact (label_eq_iff r ht hk).mp hlab
      · rintro ⟨h1, h2⟩
        have ht : t < prefixSum r m :=
          lt_of_lt_of_le h2 (prefixSum_mono r (show k + 1 ≤ m by omega))
        exact ⟨ht, (label_eq_iff r ht hk).mpr ⟨h1, h2⟩⟩
    rw [hset, Nat.card_Ico, prefixSum_succ]
    omega
  · rw [Schur.contentOf_of_le r hk, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t ht hlab
    have := (label_spec r (Finset.mem_range.mp ht)).1
    omega

variable {ν₁ ν₂ : ℕ} (h : ν₁ ≤ ν₂)

/-- The tableau of shape `(ν₂, ν₁)` filled row by row with the sorted word `0^{r_0} 1^{r_1} ⋯`. -/
def sortedTableau (hsum : ∑ j, r j = ν₁ + ν₂) (hr : ∀ j, r j ≤ ν₂) :
    SemistandardYoungTableau (twoRow h) where
  entry i c := if (i, c) ∈ twoRow h then label r (i * ν₂ + c) else 0
  row_weak' := by
    intro i j₁ j₂ hj hc
    have hc₁ : (i, j₁) ∈ twoRow h := (twoRow h).up_left_mem le_rfl hj.le hc
    rw [ite_eq_left hc₁, ite_eq_left hc]
    exact label_mono r (by omega)
  col_strict' := by
    intro i₁ i₂ j hi hc
    have hc₁ : (i₁, j) ∈ twoRow h := (twoRow h).up_left_mem hi.le le_rfl hc
    rw [ite_eq_left hc₁, ite_eq_left hc]
    have hm1 := (mem_twoRow h).mp hc₁
    have hm2 := (mem_twoRow h).mp hc
    have hi₁ : i₁ = 0 := by omega
    have hi₂ : i₂ = 1 := by omega
    subst hi₁ hi₂
    have hj : j < ν₁ := by omega
    have hN : prefixSum r m = ν₁ + ν₂ := by rw [prefixSum_m, hsum]
    refine lt_of_le_of_ne (label_mono r (by omega)) fun heq => ?_
    simp only [zero_mul, zero_add, one_mul] at heq
    obtain ⟨hL, h1, h2⟩ := label_spec r (show j < prefixSum r m by omega)
    obtain ⟨hL', h1', h2'⟩ := label_spec r (show ν₂ + j < prefixSum r m by omega)
    rw [← heq] at h2'
    have hk := prefixSum_succ r (label r j)
    have hc : Schur.contentOf r (label r j) = r ⟨label r j, hL⟩ := by
      simp [Schur.contentOf, hL]
    have := hr ⟨label r j, hL⟩
    omega
  zeros' := by
    intro i j hc
    exact ite_eq_right hc

theorem content_sortedTableau (hsum : ∑ j, r j = ν₁ + ν₂) (hr : ∀ j, r j ≤ ν₂) :
    ⇑(SemistandardYoungTableau.content (sortedTableau r h hsum hr)) = Schur.contentOf r := by
  funext k
  rw [SemistandardYoungTableau.content_apply, ← card_label_eq r k,
    show prefixSum r m = ν₂ + ν₁ by rw [prefixSum_m, hsum, add_comm]]
  refine Finset.card_nbij' (fun ic => ic.1 * ν₂ + ic.2)
    (fun t => if t < ν₂ then (0, t) else (1, t - ν₂)) ?_ ?_ ?_ ?_
  · intro ic hic
    simp only [Finset.mem_coe, Finset.mem_filter, YoungDiagram.mem_cells] at hic
    obtain ⟨hmem, hent⟩ := hic
    have hm := (mem_twoRow h).mp hmem
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
    refine ⟨by rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;> omega, ?_⟩
    have := hent
    change (if (ic.1, ic.2) ∈ twoRow h then label r (ic.1 * ν₂ + ic.2) else 0) = k at this
    rwa [ite_eq_left hmem] at this
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ht
    obtain ⟨ht1, ht2⟩ := ht
    simp only [Finset.mem_coe, Finset.mem_filter, YoungDiagram.mem_cells]
    by_cases htν : t < ν₂
    · simp only [htν, ↓reduceIte]
      have hmem : ((0, t) : ℕ × ℕ) ∈ twoRow h := (mem_twoRow h).mpr (Or.inl ⟨rfl, htν⟩)
      refine ⟨hmem, ?_⟩
      change (if ((0 : ℕ), t) ∈ twoRow h then label r (0 * ν₂ + t) else 0) = k
      rw [ite_eq_left hmem, zero_mul, zero_add, ht2]
    · simp only [htν, ↓reduceIte]
      have hmem : ((1, t - ν₂) : ℕ × ℕ) ∈ twoRow h :=
        (mem_twoRow h).mpr (Or.inr ⟨rfl, by omega⟩)
      refine ⟨hmem, ?_⟩
      change (if ((1 : ℕ), t - ν₂) ∈ twoRow h then label r (1 * ν₂ + (t - ν₂)) else 0) = k
      rw [ite_eq_left hmem, one_mul, show ν₂ + (t - ν₂) = t by omega, ht2]
  · intro ic hic
    simp only [Finset.mem_coe, Finset.mem_filter, YoungDiagram.mem_cells] at hic
    have hm := (mem_twoRow h).mp hic.1
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨i, c⟩ := ic
      simp only at h1 h2
      subst h1
      simp [h2]
    · obtain ⟨i, c⟩ := ic
      simp only at h1 h2
      subst h1
      simp only [one_mul, show ¬ ν₂ + c < ν₂ by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at ht
    by_cases htν : t < ν₂
    · simp [htν]
    · simp only [htν, ↓reduceIte, one_mul]
      omega

/-- **Two-row Kostka numbers** (the support criterion in the proof of Proposition 5.8): if
`∑_j r_j = ν₁ + ν₂` and `ν₁ ≤ ν₂`, a tableau of shape `(ν₂, ν₁)` and content `r` exists exactly
when every `r_j ≤ ν₂`. -/
theorem kostka_twoRow_pos_iff (hsum : ∑ j, r j = ν₁ + ν₂) :
    0 < TauCeti.diagramKostkaNumber (twoRow h) (Schur.contentOf r) ↔ ∀ j, r j ≤ ν₂ := by
  constructor
  · intro hpos j
    obtain ⟨T, hT⟩ := TauCeti.diagramKostkaNumber_ne_zero_iff.mp hpos.ne'
    have hj := congrFun hT j
    rw [SemistandardYoungTableau.content_apply] at hj
    have hcj : Schur.contentOf r j = r j := by simp [Schur.contentOf, j.isLt]
    rw [← hcj, ← hj]
    calc ((twoRow h).cells.filter fun c => T c.1 c.2 = j).card
        ≤ (Finset.range ν₂).card := by
          refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
          · intro ic hic
            simp only [Finset.mem_coe, Finset.mem_filter, YoungDiagram.mem_cells] at hic
            have hm := (mem_twoRow h).mp hic.1
            simp only [Finset.coe_range, Set.mem_Iio]
            omega
          · intro ic hic ic' hic' heq
            simp only [Finset.mem_coe, Finset.mem_filter, YoungDiagram.mem_cells] at hic hic'
            obtain ⟨i, c⟩ := ic
            obtain ⟨i', c'⟩ := ic'
            simp only at heq hic hic'
            subst heq
            have hm := (mem_twoRow h).mp hic.1
            have hm' := (mem_twoRow h).mp hic'.1
            by_contra hne
            have hii' : i ≠ i' := fun e => hne (by rw [e])
            rcases Nat.lt_or_gt_of_ne hii' with hlt | hlt
            · have := T.col_strict hlt hic'.1
              omega
            · have := T.col_strict hlt hic.1
              omega
      _ = ν₂ := Finset.card_range ν₂
  · intro hr
    exact Nat.pos_of_ne_zero (TauCeti.diagramKostkaNumber_ne_zero_iff.mpr
      ⟨sortedTableau r h hsum hr, content_sortedTableau r h hsum hr⟩)

end TwoRowKostka

/-! ## Proposition 5.8 -/

section Main

variable {a b c : Composition (m + 2)} {N : ℕ} {ν₁ ν₂ : ℕ} {r : Fin m → ℕ}

/-- The degree equality for the two-source pattern: `∑_j r_j = ν₁ + ν₂`. -/
theorem sum_eq_of_twoSource (hW : Window.Hypotheses a b c N)
    (hν₁ : Window.residual a b c 0 = ν₁) (hν₂ : Window.residual a b c 1 = ν₂)
    (hr : ∀ j, Window.residual a b c (singletonPos j) = -(r j : ℤ)) :
    ∑ j, r j = ν₁ + ν₂ := by
  have h := Window.sum_residual_eq_zero hW.balance
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h
  have e1 : (Fin.succ 0 : Fin (m + 2)) = 1 := rfl
  rw [e1, hν₁, hν₂] at h
  have hs : ∑ j : Fin m, Window.residual a b c j.succ.succ = -((∑ j, r j : ℕ) : ℤ) := by
    rw [Nat.cast_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hr j]
    rfl
  rw [hs] at h
  omega

/-- **Proposition 5.8 of the paper** (`prop:quiver-two-source`), tableau form: under the star
pattern (5.9), with `ν = (ν₁, ν₂, −r₁, …, −r_m)` and `0 ≤ ν₁ ≤ ν₂`, the atom coefficient counts the
semistandard tableaux of shape `(ν₂, ν₁)` and content `r`. -/
theorem twoSource_eq_kostka (h : ν₁ ≤ ν₂) (hW : Window.Hypotheses a b c N)
    (hstar : ∀ i j : Fin (m + 2), i < j →
      Window.cmp (Window.triple a b (Window.complement N c) i)
        (Window.triple a b (Window.complement N c) j) = starPattern i j)
    (hν₁ : Window.residual a b c 0 = ν₁) (hν₂ : Window.residual a b c 1 = ν₂)
    (hr : ∀ j, Window.residual a b c (singletonPos j) = -(r j : ℤ)) :
    atomCoefficient (key a * key b) c =
      TauCeti.diagramKostkaNumber (twoRow h) (Schur.contentOf r) := by
  rw [twoSource_eq_weylProjector hW hstar hν₁ hν₂ hr]
  have hY := Schur.weylProjector_hProd (d := 2) r (twoRowWeight h)
  have hu : (twoRowWeight h).1 ∘ ⇑(Fin.revPerm : Equiv.Perm (Fin 2)) = ![(ν₁ : ℤ), ν₂] := by
    funext i
    fin_cases i <;> rfl
  rw [hu, Schur.hProd] at hY
  rw [hY, Schur.kostkaZ, ite_eq_left (isPolynomial_twoRowWeight h)]
  rfl

/-- **The support of the two-source formula** (5.11): the atom coefficient is positive exactly
when every `r_j ≤ ν₂`. -/
theorem twoSource_pos_iff (h : ν₁ ≤ ν₂) (hW : Window.Hypotheses a b c N)
    (hstar : ∀ i j : Fin (m + 2), i < j →
      Window.cmp (Window.triple a b (Window.complement N c) i)
        (Window.triple a b (Window.complement N c) j) = starPattern i j)
    (hν₁ : Window.residual a b c 0 = ν₁) (hν₂ : Window.residual a b c 1 = ν₂)
    (hr : ∀ j, Window.residual a b c (singletonPos j) = -(r j : ℤ)) :
    0 < atomCoefficient (key a * key b) c ↔ ∀ j, r j ≤ ν₂ := by
  rw [twoSource_eq_kostka h hW hstar hν₁ hν₂ hr, Nat.cast_pos]
  exact kostka_twoRow_pos_iff r h (sum_eq_of_twoSource hW hν₁ hν₂ hr)

end Main

end

end Schubert.RS.Quiver
