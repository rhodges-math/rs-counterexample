import RSCounterexample.Paper.Hall.Partition
import RSCounterexample.Paper.Hall.Determinant
import RSCounterexample.Paper.Hall.FiniteWindow
import RSCounterexample.Paper.Hall.Substitution

/-!
# Coefficient extraction for Hall triples

Proposition 3.11 of the paper (`prop:paired-reduction`). Let `(a, b, c)` be a Hall triple with an
`r`-Hall partition `𝓑` and distinguished blocks `B_1, …, B_r`. With the non-distinguished positions
`q_1 < ⋯ < q_m`, the pairs `𝓔` and the Hall polynomials `P_s` of the blocks,

`[𝒜_c](κ_a κ_b) = [t_1 ⋯ t_m] ∏_{s=1}^r P_s(t_1, …, t_m) ∏_{(i,j) ∈ 𝓔} (1 − t_j/t_i)`.

The proof follows the paper. Proposition 2.13 gives the coefficient of `x^{c−a−b}` in
`∏_{u<v} (1 − x_u/x_v)^{−cmp_{uv}}` (`atomCoefficient_eq_finiteCmpFactor`, with every geometric
series truncated in a degree beyond the window). Substituting `x_{q_j} = t_j^{−1}`
(`substitute`), condition (ii) groups the factors into one factor per distinguished block,
`Δ(x_{B_s}) ∏_j ∏_{u ∈ B_s, u < q_j} (1 − x_u t_j)^{−1}`, and the factors `1 − t_j/t_i` of the pairs
(`substitute_rootProduct`). The variables of each block occur only in its own factor, so the
coefficient of `∏_{u ∈ B_s} x_u` is extracted blockwise (`coeff_prod_mapDomain`), and Lemma 3.1
(`hall_determinant`) with Lemma 3.8 (`hall_flags`) evaluates each blockwise coefficient as `P_s`.

## Main results

* `Schubert.RS.Hall.paired_reduction`: Proposition 3.11, (3.12) (eq:paired-coefficient).
* `Schubert.RS.Hall.paired_reduction_of_isHallTriple`: the same for a Hall triple, with some
  Hall partition.
-/

namespace Schubert.RS.Hall

noncomputable section

open AddMonoidAlgebra Window Representation

variable {n m : ℕ}

/-! ### Generalities -/

/-- The Laurent polynomials in the positions with coefficients Laurent polynomials in
`t_0, …, t_{m−1}`. -/
abbrev TwoLayer (m n : ℕ) : Type := AddMonoidAlgebra (Laurent m) (Weight n)

/-- The variable `t_j`. -/
def tVar (j : Fin m) : Laurent m := single (Pi.single j 1) 1

theorem tVar_pow (j : Fin m) (k : ℕ) : tVar j ^ k = single (Pi.single j (k : ℤ)) 1 := by
  rw [tVar, single_pow, one_pow]
  congr 1
  funext j'
  by_cases h : j' = j
  · subst h
    simp
  · simp [h]

/-- `∑_{k ≤ B} (x_u t_j)^k`, the geometric series `(1 − x_u t_j)^{−1}` truncated in degree `B`. -/
def geomFactor (B : ℕ) (u : Fin n) (j : Fin m) : TwoLayer m n :=
  ∑ k : Fin (B + 1), single (Pi.single u (k.val : ℤ)) (tVar j ^ k.val)

theorem prod_ite_mem_univ {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (S : Finset ι) (f : ι → M) : ∏ i, (if i ∈ S then f i else 1) = ∏ i ∈ S, f i := by
  rw [Finset.prod_ite_mem, Finset.univ_inter]

theorem prod_prod_ite_mem {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (S : Finset ι) (f : ι → ι → M) :
    ∏ u, ∏ v, (if u ∈ S ∧ v ∈ S then f u v else 1) = ∏ u ∈ S, ∏ v ∈ S, f u v := by
  rw [← prod_ite_mem_univ S]
  refine Finset.prod_congr rfl fun u _ => ?_
  by_cases hu : u ∈ S
  · simp only [hu, true_and, ite_true]
    exact prod_ite_mem_univ S _
  · simp [hu]

theorem prod_comm_three {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [CommMonoid M]
    (f : α → β → γ → M) : ∏ a, ∏ b, ∏ c, f a b c = ∏ c, ∏ a, ∏ b, f a b c := by
  calc ∏ a, ∏ b, ∏ c, f a b c = ∏ ab : α × β, ∏ c, f ab.1 ab.2 c := by
        rw [Fintype.prod_prod_type]
    _ = ∏ c, ∏ ab : α × β, f ab.1 ab.2 c := Finset.prod_comm
    _ = ∏ c, ∏ a, ∏ b, f a b c := by
        simp only [Fintype.prod_prod_type]

theorem prod_comm_four {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [CommMonoid M] (f : α → β → γ → δ → M) :
    ∏ a, ∏ b, ∏ c, ∏ d, f a b c d = ∏ c, ∏ d, ∏ a, ∏ b, f a b c d := by
  calc ∏ a, ∏ b, ∏ c, ∏ d, f a b c d = ∏ ab : α × β, ∏ cd : γ × δ, f ab.1 ab.2 cd.1 cd.2 := by
        simp only [Fintype.prod_prod_type]
    _ = ∏ cd : γ × δ, ∏ ab : α × β, f ab.1 ab.2 cd.1 cd.2 := Finset.prod_comm
    _ = ∏ c, ∏ d, ∏ a, ∏ b, f a b c d := by
        simp only [Fintype.prod_prod_type]

/-- For an increasing enumeration `u_0 < ⋯ < u_{d−1}` of `S`, `u_a < y` exactly when `a` is less
than the number of elements of `S` below `y`. -/
theorem orderEmbOfFin_lt_iff (S : Finset (Fin n)) (a : Fin S.card) (y : Fin n) :
    S.orderEmbOfFin rfl a < y ↔ a.val < (S.filter (· < y)).card := by
  classical
  set u := S.orderEmbOfFin rfl
  have hr : Set.range u = S := Finset.range_orderEmbOfFin S rfl
  have hcard : (S.filter (· < y)).card = (Finset.univ.filter fun a' => u a' < y).card := by
    rw [← Finset.card_image_of_injective _ u.injective]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hxy⟩
      have hx' : x ∈ Set.range u := by
        rw [hr]
        exact hx
      obtain ⟨a', rfl⟩ := hx'
      exact ⟨a', hxy, rfl⟩
    · rintro ⟨a', ha', rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem S rfl a', ha'⟩
  rw [hcard]
  constructor
  · intro h
    have hsub : Finset.Iic a ⊆ Finset.univ.filter fun a' => u a' < y := fun a' ha' => by
      simp only [Finset.mem_Iic] at ha'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (u.monotone ha').trans_lt h
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro h
    by_contra hn
    have hsub : (Finset.univ.filter fun a' => u a' < y) ⊆ Finset.Iio a := fun a' ha' => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha'
      simp only [Finset.mem_Iio]
      by_contra h'
      exact hn ((u.monotone (not_lt.mp h')).trans_lt ha')
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/-! ### Blocks of the Hall product -/

section Blocks

variable {d : ℕ} (u : Fin d → Fin n)

theorem mapDomain_weylFactor :
    mapDomainRingHom (Laurent m) (blockEmbed u)
        (mapRingHom (Weight d) (Int.castRingHom (Laurent m)) (weylFactor d)) =
      ∏ a : Fin d, ∏ b ∈ Finset.univ.filter (a < ·),
        (1 - single (positiveRoot (u a) (u b)) 1 : TwoLayer m n) := by
  simp only [weylFactor, map_prod, map_sub, map_one, mapRingHom_single, mapDomainRingHom_apply,
    mapDomain_single, blockEmbed_positiveRoot]

theorem mapDomain_geomTerm (a : Fin d) (j : Fin m) (B : ℕ) :
    mapDomainRingHom (Laurent m) (blockEmbed u) (geomTerm a (tVar j) B) =
      geomFactor B (u a) j := by
  simp only [geomTerm, geomFactor, map_sum, mapDomainRingHom_apply, mapDomain_single,
    blockEmbed_single]

end Blocks

namespace HallPartition

variable {a b c : Composition n} {N r : ℕ} (P : HallPartition a b c N r)

/-! ### The positions of the blocks -/

/-- The elements `u_1 < ⋯ < u_d` of `B_s`. -/
def blockPos (s : Fin r) : Fin (P.dist s).card ↪o Fin n := (P.dist s).orderEmbOfFin rfl

theorem blockPos_mem (s : Fin r) (k : Fin (P.dist s).card) : P.blockPos s k ∈ P.dist s :=
  Finset.orderEmbOfFin_mem _ _ k

theorem exists_blockPos {s : Fin r} {i : Fin n} (hi : i ∈ P.dist s) : ∃ k, P.blockPos s k = i := by
  have h := Finset.range_orderEmbOfFin (P.dist s) rfl
  have : i ∈ Set.range (P.blockPos s) := by
    change i ∈ Set.range ((P.dist s).orderEmbOfFin rfl)
    rw [h]
    exact hi
  exact this

theorem blockPos_lt_q_iff (s : Fin r) (k : Fin (P.dist s).card) (j : Fin P.m) :
    P.blockPos s k < P.q j ↔ k.val < P.height s j :=
  orderEmbOfFin_lt_iff _ _ _

theorem prod_dist {M : Type*} [CommMonoid M] (s : Fin r) (f : Fin n → M) :
    ∏ x ∈ P.dist s, f x = ∏ k, f (P.blockPos s k) := by
  have himg : Finset.univ.image (P.blockPos s) = P.dist s :=
    Finset.image_orderEmbOfFin_univ _ _
  have h := Finset.prod_image (s := Finset.univ) (f := f) (g := P.blockPos s)
    fun x _ y _ hxy => (P.blockPos s).injective hxy
  rw [himg] at h
  exact h

theorem q_mem_compl (j : Fin P.m) : P.q j ∈ P.distinguishedᶜ :=
  Finset.mem_compl.mpr (P.q_not_mem j)

theorem dist_subset (s : Fin r) : P.dist s ⊆ P.distinguished := fun _ hi =>
  P.mem_distinguished.mpr ⟨s, hi⟩

theorem q_not_mem_dist (s : Fin r) (j : Fin P.m) : P.q j ∉ P.dist s := fun h =>
  P.q_not_mem j (P.dist_subset s h)

theorem eq_of_mem_dist {s s' : Fin r} {i : Fin n} (h : i ∈ P.dist s) (h' : i ∈ P.dist s') :
    s = s' := by
  by_contra hne
  exact Finset.disjoint_left.mp (P.dist_disjoint hne) h h'

/-! ### The substituted root factors -/

theorem substitute_weyl {u v : Fin n} (hu : u ∈ P.distinguished) (hv : v ∈ P.distinguished) :
    substitute P.distinguished P.q (1 - single (positiveRoot u v) 1) =
      (1 - single (positiveRoot u v) 1 : TwoLayer P.m n) := by
  rw [map_sub, map_one, substitute_single]
  have h1 : (splitWeight P.distinguished P.q (positiveRoot u v)).1 = positiveRoot u v := by
    funext i
    rw [splitWeight_fst]
    split_ifs with hi
    · rfl
    · have hiu : i ≠ u := fun h => hi (h ▸ hu)
      have hiv : i ≠ v := fun h => hi (h ▸ hv)
      simp [positiveRoot, hiu, hiv]
  have h2 : (splitWeight P.distinguished P.q (positiveRoot u v)).2 = 0 := by
    funext j
    have hju : P.q j ≠ u := fun h => P.q_not_mem j (h ▸ hu)
    have hjv : P.q j ≠ v := fun h => P.q_not_mem j (h ▸ hv)
    simp [positiveRoot, hju, hjv]
  rw [h1, h2]
  rfl

theorem substitute_geom (B : ℕ) {u : Fin n} (hu : u ∈ P.distinguished) (j : Fin P.m) :
    substitute P.distinguished P.q
        (∑ k : Fin (B + 1), single (k.val • positiveRoot u (P.q j)) 1) =
      geomFactor B u j := by
  rw [map_sum, geomFactor]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [substitute_single, tVar_pow]
  have hju : P.q j ≠ u := fun h => P.q_not_mem j (h ▸ hu)
  have h1 : (splitWeight P.distinguished P.q (k.val • positiveRoot u (P.q j))).1 =
      Pi.single u (k.val : ℤ) := by
    funext i
    rw [splitWeight_fst]
    split_ifs with hi
    · have hiq : i ≠ P.q j := fun h => P.q_not_mem j (h ▸ hi)
      by_cases hiu : i = u
      · subst hiu
        simp [positiveRoot, hiq]
      · simp [positiveRoot, hiu, hiq]
    · have hiu : i ≠ u := fun h => hi (h ▸ hu)
      simp [hiu]
  have h2 : (splitWeight P.distinguished P.q (k.val • positiveRoot u (P.q j))).2 =
      Pi.single j (k.val : ℤ) := by
    funext j'
    rw [splitWeight_snd]
    have hj'u : P.q j' ≠ u := fun h => P.q_not_mem j' (h ▸ hu)
    by_cases hj' : j' = j
    · subst hj'
      simp [positiveRoot, hj'u]
    · have hq : P.q j' ≠ P.q j := fun h => hj' (P.q.injective h)
      simp [positiveRoot, hj'u, hq, hj']
  rw [h1, h2]

theorem substitute_pair (i j : Fin P.m) :
    substitute P.distinguished P.q (1 - single (positiveRoot (P.q i) (P.q j)) 1) =
      (single 0 (1 - single (Pi.single j 1 - Pi.single i 1) 1) : TwoLayer P.m n) := by
  rw [map_sub, map_one, substitute_single]
  have h1 : (splitWeight P.distinguished P.q (positiveRoot (P.q i) (P.q j))).1 = 0 := by
    funext x
    rw [splitWeight_fst]
    split_ifs with hx
    · have hxi : x ≠ P.q i := fun h => P.q_not_mem i (h ▸ hx)
      have hxj : x ≠ P.q j := fun h => P.q_not_mem j (h ▸ hx)
      simp [positiveRoot, hxi, hxj]
    · rfl
  have h2 : (splitWeight P.distinguished P.q (positiveRoot (P.q i) (P.q j))).2 =
      Pi.single j 1 - Pi.single i 1 := by
    funext j'
    rw [splitWeight_snd]
    simp only [positiveRoot, Pi.sub_apply, Pi.single_apply, P.q.injective.eq_iff]
    split_ifs <;> simp
  rw [h1, h2, single_sub, ← one_def]

/-! ### Sorting the root factors by condition (ii) -/

theorem mem_pairs {i j : Fin P.m} :
    (i, j) ∈ P.pairs ↔ i < j ∧ ({P.q i, P.q j} : Finset (Fin n)) ∈ P.blocks.parts ∧
      ∀ s, ({P.q i, P.q j} : Finset (Fin n)) ≠ P.dist s := by
  simp [pairs]

/-- The factor `1 − x_u/x_v` when `u` and `v` lie in a common distinguished block. -/
def weylPart (u v : Fin n) : TwoLayer P.m n :=
  ∏ s, if u ∈ P.dist s ∧ v ∈ P.dist s then (1 - single (positiveRoot u v) 1) else 1

/-- The factor `(1 − x_u t_j)^{−1}`, truncated in degree `B`, when `u` is distinguished and
`v = q_j`. -/
def geomPart (B : ℕ) (u v : Fin n) : TwoLayer P.m n :=
  ∏ s, ∏ j, if u ∈ P.dist s ∧ v = P.q j then geomFactor B u j else 1

/-- The factor `1 − t_j/t_i` when `u = q_i`, `v = q_j` and `(i, j) ∈ 𝓔`. -/
def pairPart (u v : Fin n) : TwoLayer P.m n :=
  ∏ i, ∏ j, if u = P.q i ∧ v = P.q j ∧ (i, j) ∈ P.pairs then
    single 0 (1 - single (Pi.single j 1 - Pi.single i 1) 1) else 1

theorem weylPart_of_mem {s₀ : Fin r} {u v : Fin n} (hu : u ∈ P.dist s₀) (hv : v ∈ P.dist s₀) :
    P.weylPart u v = 1 - single (positiveRoot u v) 1 := by
  unfold weylPart
  rw [Finset.prod_eq_single s₀]
  · exact ite_eq_left ⟨hu, hv⟩
  · intro s _ hs
    exact ite_eq_right fun h => hs (P.eq_of_mem_dist h.1 hu)
  · simp

theorem weylPart_eq_one {u v : Fin n} (h : ∀ s, ¬ (u ∈ P.dist s ∧ v ∈ P.dist s)) :
    P.weylPart u v = 1 :=
  Finset.prod_eq_one fun s _ => ite_eq_right (h s)

theorem geomPart_of_mem (B : ℕ) {s₀ : Fin r} {u : Fin n} (hu : u ∈ P.dist s₀) (j₀ : Fin P.m) :
    P.geomPart B u (P.q j₀) = geomFactor B u j₀ := by
  unfold geomPart
  rw [Finset.prod_eq_single s₀]
  · rw [Finset.prod_eq_single j₀]
    · exact ite_eq_left ⟨hu, rfl⟩
    · intro j _ hj
      exact ite_eq_right fun h => hj (P.q.injective h.2.symm)
    · simp
  · intro s _ hs
    exact Finset.prod_eq_one fun j _ => ite_eq_right fun h => hs (P.eq_of_mem_dist h.1 hu)
  · simp

theorem geomPart_eq_one (B : ℕ) {u v : Fin n} (h : ∀ s j, ¬ (u ∈ P.dist s ∧ v = P.q j)) :
    P.geomPart B u v = 1 :=
  Finset.prod_eq_one fun s _ => Finset.prod_eq_one fun j _ => ite_eq_right (h s j)

theorem pairPart_of_mem {i₀ j₀ : Fin P.m} (h : (i₀, j₀) ∈ P.pairs) :
    P.pairPart (P.q i₀) (P.q j₀) =
      single 0 (1 - single (Pi.single j₀ 1 - Pi.single i₀ 1) 1) := by
  unfold pairPart
  rw [Finset.prod_eq_single i₀]
  · rw [Finset.prod_eq_single j₀]
    · exact ite_eq_left ⟨rfl, rfl, h⟩
    · intro j _ hj
      exact ite_eq_right fun h' => hj (P.q.injective h'.2.1.symm)
    · simp
  · intro i _ hi
    exact Finset.prod_eq_one fun j _ => ite_eq_right fun h' => hi (P.q.injective h'.1.symm)
  · simp

theorem pairPart_eq_one {u v : Fin n}
    (h : ∀ i j, ¬ (u = P.q i ∧ v = P.q j ∧ (i, j) ∈ P.pairs)) : P.pairPart u v = 1 :=
  Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ite_eq_right (h i j)

/-- Each root factor after the substitution, sorted by condition (ii) of Definition 3.9. -/
theorem substitute_finiteCmpFactor (B : ℕ) {u v : Fin n} (huv : u < v) :
    substitute P.distinguished P.q (finiteCmpFactor B
        (cmp (triple a b (complement N c) u) (triple a b (complement N c) v)) u v) =
      P.weylPart u v * P.geomPart B u v * P.pairPart u v := by
  rw [P.cmp_eq u v huv]
  by_cases hsame : ∃ B ∈ P.blocks.parts, u ∈ B ∧ v ∈ B
  · rw [ite_eq_left hsame]
    have hF : finiteCmpFactor B (-1) u v = 1 - single (positiveRoot u v) 1 := by
      simp [finiteCmpFactor]
    rw [hF]
    by_cases huD : u ∈ P.distinguished
    · obtain ⟨s₀, hs₀⟩ := P.mem_distinguished.mp huD
      have hv : v ∈ P.dist s₀ := (P.sameBlock_iff_of_mem_dist hs₀ v).mp hsame
      have hG : P.geomPart B u v = 1 :=
        P.geomPart_eq_one B fun s j h => P.q_not_mem_dist s₀ j (h.2 ▸ hv)
      have hP : P.pairPart u v = 1 :=
        P.pairPart_eq_one fun i j h => P.q_not_mem i (h.1 ▸ huD)
      rw [P.weylPart_of_mem hs₀ hv, hG, hP, mul_one, mul_one,
        P.substitute_weyl huD (P.dist_subset s₀ hv)]
    · have hvD : v ∉ P.distinguished := by
        intro hvD
        obtain ⟨s₀, hs₀⟩ := P.mem_distinguished.mp hvD
        obtain ⟨B', hB', huB, hvB⟩ := hsame
        have he := P.blocks.eq_of_mem_parts hB' (P.dist_mem s₀) hvB hs₀
        exact huD (P.dist_subset s₀ (he ▸ huB))
      obtain ⟨i₀, rfl⟩ := P.exists_q huD
      obtain ⟨j₀, rfl⟩ := P.exists_q hvD
      have hmem : (i₀, j₀) ∈ P.pairs := by
        rw [P.mem_pairs]
        exact ⟨P.q.lt_iff_lt.mp huv, (P.sameBlock_iff_of_not_mem huD huv.ne).mp hsame⟩
      have hW : P.weylPart (P.q i₀) (P.q j₀) = 1 :=
        P.weylPart_eq_one fun s h => P.q_not_mem_dist s i₀ h.1
      have hG : P.geomPart B (P.q i₀) (P.q j₀) = 1 :=
        P.geomPart_eq_one B fun s j h => P.q_not_mem_dist s i₀ h.1
      rw [hW, hG, P.pairPart_of_mem hmem, one_mul, one_mul, P.substitute_pair]
  · rw [ite_eq_right hsame]
    by_cases hcross : (∃ s, u ∈ P.dist s) ∧ ¬ ∃ s, v ∈ P.dist s
    · rw [ite_eq_left hcross]
      have hF : finiteCmpFactor B 1 u v =
          ∑ k : Fin (B + 1), single (k.val • positiveRoot u v) 1 := by
        simp [finiteCmpFactor]
      rw [hF]
      obtain ⟨⟨s₀, hs₀⟩, hv⟩ := hcross
      have hvD : v ∉ P.distinguished := fun h => hv (P.mem_distinguished.mp h)
      obtain ⟨j₀, rfl⟩ := P.exists_q hvD
      have hW : P.weylPart u (P.q j₀) = 1 := P.weylPart_eq_one fun s h => hv ⟨s, h.2⟩
      have hP : P.pairPart u (P.q j₀) = 1 :=
        P.pairPart_eq_one fun i j h => P.q_not_mem i (h.1 ▸ P.dist_subset s₀ hs₀)
      rw [hW, P.geomPart_of_mem B hs₀ j₀, hP, one_mul, mul_one,
        P.substitute_geom B (P.dist_subset s₀ hs₀)]
    · rw [ite_eq_right hcross]
      have hF : finiteCmpFactor B 0 u v = 1 := by
        simp [finiteCmpFactor]
      have hW : P.weylPart u v = 1 := P.weylPart_eq_one fun s h =>
        hsame ⟨_, P.dist_mem s, h.1, h.2⟩
      have hG : P.geomPart B u v = 1 := P.geomPart_eq_one B fun s j h => by
        obtain ⟨hu, rfl⟩ := h
        exact hcross ⟨⟨s, hu⟩, fun ⟨s', hs'⟩ => P.q_not_mem_dist s' j hs'⟩
      have hP : P.pairPart u v = 1 := P.pairPart_eq_one fun i j h => by
        obtain ⟨rfl, rfl, h⟩ := h
        exact hsame ⟨_, ((P.mem_pairs).mp h).2.1, by simp, by simp⟩
      rw [hF, map_one, hW, hG, hP, mul_one, mul_one]

/-! ### Regrouping the factors -/

theorem prod_weylPart :
    ∏ u : Fin n, ∏ v : Fin n, (if u < v then P.weylPart u v else 1) =
      ∏ s, ∏ k : Fin (P.dist s).card, ∏ l ∈ Finset.univ.filter (k < ·),
        (1 - single (positiveRoot (P.blockPos s k) (P.blockPos s l)) 1 : TwoLayer P.m n) := by
  have hpt : ∀ u v : Fin n, (if u < v then P.weylPart u v else 1) =
      ∏ s, if u ∈ P.dist s ∧ v ∈ P.dist s then
        (if u < v then (1 - single (positiveRoot u v) 1 : TwoLayer P.m n) else 1) else 1 := by
    intro u v
    by_cases huv : u < v
    · simp only [huv, ite_true, weylPart]
    · simp [huv]
  rw [Finset.prod_congr rfl fun u _ => Finset.prod_congr rfl fun v _ => hpt u v,
    prod_comm_three]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [prod_prod_ite_mem, P.prod_dist s]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [P.prod_dist s, Finset.prod_filter]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp only [(P.blockPos s).lt_iff_lt]

theorem prod_geomPart (B : ℕ) :
    ∏ u : Fin n, ∏ v : Fin n, (if u < v then P.geomPart B u v else 1) =
      ∏ s, ∏ j, ∏ k ∈ Finset.univ.filter (fun k : Fin (P.dist s).card => k.val < P.height s j),
        geomFactor B (P.blockPos s k) j := by
  have hpt : ∀ u v : Fin n, (if u < v then P.geomPart B u v else 1) =
      ∏ s, ∏ j, if u ∈ P.dist s ∧ v = P.q j then
        (if u < v then geomFactor B u j else 1) else 1 := by
    intro u v
    by_cases huv : u < v
    · simp only [huv, ite_true, geomPart]
    · simp [huv]
  rw [Finset.prod_congr rfl fun u _ => Finset.prod_congr rfl fun v _ => hpt u v,
    prod_comm_four]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun j _ => ?_
  have hinner : ∀ u : Fin n, ∏ v : Fin n, (if u ∈ P.dist s ∧ v = P.q j then
      (if u < v then geomFactor B u j else 1) else 1) =
      if u ∈ P.dist s then (if u < P.q j then geomFactor B u j else 1) else 1 := by
    intro u
    by_cases hu : u ∈ P.dist s
    · simp only [hu, true_and, ite_true]
      rw [Finset.prod_ite_eq']
      simp
    · simp [hu]
  rw [Finset.prod_congr rfl fun u _ => hinner u, prod_ite_mem_univ, P.prod_dist s,
    Finset.prod_filter]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [P.blockPos_lt_q_iff]

theorem prod_prod_ite_eq {ι κ M : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [CommMonoid M] (x₀ : ι) (y₀ : κ) (f : ι → κ → M) :
    ∏ x, ∏ y, (if x = x₀ then (if y = y₀ then f x y else 1) else 1) = f x₀ y₀ := by
  rw [Finset.prod_eq_single x₀]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

theorem prod_pairPart :
    ∏ u : Fin n, ∏ v : Fin n, (if u < v then P.pairPart u v else 1) =
      single 0 (∏ ij ∈ P.pairs, (1 - single (Pi.single ij.2 1 - Pi.single ij.1 1) 1)) := by
  have hpt : ∀ u v : Fin n, (if u < v then P.pairPart u v else 1) =
      ∏ i, ∏ j, if u = P.q i then (if v = P.q j then (if (i, j) ∈ P.pairs then
        (single 0 (1 - single (Pi.single j 1 - Pi.single i 1) 1) : TwoLayer P.m n) else 1)
        else 1) else 1 := by
    intro u v
    have hp : (if u < v then P.pairPart u v else 1) = P.pairPart u v := by
      by_cases huv : u < v
      · exact ite_eq_left huv
      · rw [ite_eq_right huv]
        refine (P.pairPart_eq_one fun i j h => huv ?_).symm
        obtain ⟨rfl, rfl, h⟩ := h
        exact P.q.lt_iff_lt.mpr ((P.mem_pairs).mp h).1
    rw [hp, pairPart]
    simp only [ite_and]
  rw [Finset.prod_congr rfl fun u _ => Finset.prod_congr rfl fun v _ => hpt u v,
    prod_comm_four]
  simp only [prod_prod_ite_eq]
  have hR : (single 0 (∏ ij ∈ P.pairs, (1 - single (Pi.single ij.2 1 - Pi.single ij.1 1) 1 :
      Laurent P.m)) : TwoLayer P.m n) =
      ∏ ij ∈ P.pairs, single 0 (1 - single (Pi.single ij.2 1 - Pi.single ij.1 1) 1) := by
    rw [AddMonoidAlgebra.prod_single, Finset.sum_const_zero]
  rw [hR, ← prod_ite_mem_univ P.pairs, Fintype.prod_prod_type]

/-- **The factorization of the substituted product** (the first equality of (3.14),
eq:hall-factorized-extraction): after substituting `x_{q_j} = t_j^{−1}`, the root product is the
product over the distinguished blocks of `Δ(x_{B_s}) ∏_j ∏_{u ∈ B_s, u < q_j} (1 − x_u t_j)^{−1}`,
written as the Hall product of Lemma 3.1 for the heights `ℓ_{s,1}, …, ℓ_{s,m}` placed at the
positions of `B_s`, times `∏_{(i,j) ∈ 𝓔} (1 − t_j/t_i)`. -/
theorem substitute_rootProduct (B : ℕ) :
    substitute P.distinguished P.q (∏ r : PositiveRoot n, finiteCmpFactor B
        (cmp (triple a b (complement N c) r.val.1) (triple a b (complement N c) r.val.2))
        r.val.1 r.val.2) =
      (∏ s, mapDomainRingHom (Laurent P.m) (blockEmbed (P.blockPos s))
          (hallProduct (d := (P.dist s).card) (P.height s) tVar B)) *
        single 0 (∏ ij ∈ P.pairs, (1 - single (Pi.single ij.2 1 - Pi.single ij.1 1) 1)) := by
  have hpr := positiveRoot_product (fun i j => finiteCmpFactor B
    (cmp (triple a b (complement N c) i) (triple a b (complement N c) j)) i j)
  rw [← hpr, map_prod]
  have hpt : ∀ u : Fin n, substitute P.distinguished P.q (∏ v ∈ Finset.univ.filter (u < ·),
      finiteCmpFactor B (cmp (triple a b (complement N c) u) (triple a b (complement N c) v)) u v) =
      ∏ v, ((if u < v then P.weylPart u v else 1) * (if u < v then P.geomPart B u v else 1) *
        (if u < v then P.pairPart u v else 1)) := by
    intro u
    rw [map_prod, Finset.prod_filter]
    refine Finset.prod_congr rfl fun v _ => ?_
    by_cases huv : u < v
    · simp only [huv, ite_true]
      exact P.substitute_finiteCmpFactor B huv
    · simp [huv]
  rw [Finset.prod_congr rfl fun u _ => hpt u]
  simp only [Finset.prod_mul_distrib]
  rw [prod_weylPart, prod_geomPart, prod_pairPart]
  congr 1
  simp only [hallProduct, map_mul, map_prod, mapDomain_weylFactor, mapDomain_geomTerm,
    Finset.prod_mul_distrib]

/-! ### The blockwise extraction -/

theorem sum_blockEmbed_apply (p : ∀ s, Weight (P.dist s).card) (s : Fin r)
    (k : Fin (P.dist s).card) :
    (∑ s', blockEmbed (P.blockPos s') (p s')) (P.blockPos s k) = p s k := by
  rw [Finset.sum_apply, Finset.sum_eq_single s]
  · exact blockEmbed_apply_self (P.blockPos s).injective _ _
  · intro s' _ hs'
    apply blockEmbed_apply_of_forall_ne
    intro k' hk'
    exact hs' (P.eq_of_mem_dist (hk' ▸ P.blockPos_mem s' k') (P.blockPos_mem s k))
  · simp

theorem sum_blockEmbed_injective :
    Function.Injective fun p : (∀ s, Weight (P.dist s).card) =>
      ∑ s, blockEmbed (P.blockPos s) (p s) := by
  intro p p' h
  funext s k
  have h' : (∑ s', blockEmbed (P.blockPos s') (p s')) (P.blockPos s k) =
      (∑ s', blockEmbed (P.blockPos s') (p' s')) (P.blockPos s k) := congrFun h _
  rwa [P.sum_blockEmbed_apply, P.sum_blockEmbed_apply] at h'

theorem splitWeight_residual_fst :
    (splitWeight P.distinguished P.q (residual a b c)).1 =
      ∑ s, blockEmbed (P.blockPos s) (fun _ => 1) := by
  funext i
  rw [splitWeight_fst]
  split_ifs with hi
  · obtain ⟨s, hs⟩ := P.mem_distinguished.mp hi
    obtain ⟨k, rfl⟩ := P.exists_blockPos hs
    have h := P.sum_blockEmbed_apply (fun _ _ => 1) s k
    rw [h, P.residual_eq, ite_eq_left ⟨s, hs⟩]
  · rw [Finset.sum_apply]
    refine (Finset.sum_eq_zero fun s _ => ?_).symm
    apply blockEmbed_apply_of_forall_ne
    intro k hk
    exact hi (hk ▸ P.dist_subset s (P.blockPos_mem s k))

theorem splitWeight_residual_snd :
    (splitWeight P.distinguished P.q (residual a b c)).2 = fun _ => 1 := by
  funext j
  rw [splitWeight_snd, P.residual_eq,
    ite_eq_right fun h => P.q_not_mem j (P.mem_distinguished.mpr h)]
  rfl

end HallPartition

/-- **Proposition 3.11 of the paper** (`prop:paired-reduction`, (3.12) eq:paired-coefficient). Let
`(a, b, c)` be a Hall triple with an `r`-Hall partition `𝓑` (for some `N ≥ max c`). With the
non-distinguished positions `q_1 < ⋯ < q_m`, the pairs `𝓔` and the Hall polynomials `P_s` of the
distinguished blocks,

`[𝒜_c](κ_a κ_b) = [t_1 ⋯ t_m] ∏_{s=1}^r P_s(t_1, …, t_m) ∏_{(i,j) ∈ 𝓔} (1 − t_j/t_i)`,

the coefficient being taken in the Laurent polynomials in `t_1, …, t_m`. -/
theorem paired_reduction {a b c : Composition n} {N r : ℕ} (P : HallPartition a b c N r) :
    atomCoefficient (key a * key b) c =
      ((∏ s, P.blockPolynomial s tVar) *
        ∏ ij ∈ P.pairs, (1 - single (Pi.single ij.2 1 - Pi.single ij.1 1) 1 : Laurent P.m)).coeff
        (fun _ => 1) := by
  set B := n + ∑ x, heightDegree a b c x
  have hB : ∀ x, heightDegree a b c x ≤ B := fun x =>
    le_add_left (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ x))
  have hd : ∀ s, (P.dist s).card ≤ B := fun s =>
    ((Finset.card_le_univ _).trans (by simp)).trans (Nat.le_add_right n _)
  rw [atomCoefficient_eq_finiteCmpFactor P.hypotheses B hB,
    ← coeff_substitute P.distinguished P.q (fun i hi => P.exists_q hi),
    P.substitute_rootProduct B, P.splitWeight_residual_fst, P.splitWeight_residual_snd,
    coeff_mul_single_zero,
    coeff_prod_mapDomain (fun s => blockEmbed (P.blockPos s)) P.sum_blockEmbed_injective]
  refine congrArg (fun f : Laurent P.m => f.coeff (fun _ => 1)) (congrArg (· * _) ?_)
  refine Finset.prod_congr rfl fun s _ => ?_
  have h := hall_determinant (d := (P.dist s).card) (P.height s) (P.height_monotone s) tVar B (hd s)
  rw [h.1, h.2, P.blockPolynomial_eq_hallAdmissible]
  rfl

/-- **Proposition 3.11 for a Hall triple**: a Hall triple has an `r`-Hall partition `P` with
`1 ≤ r ≤ n` (for some `N ≥ max c`), and for it
`[𝒜_c](κ_a κ_b) = [t_1 ⋯ t_m] ∏_s P_s(t) ∏_{(i,j) ∈ 𝓔} (1 − t_j/t_i)`. -/
theorem paired_reduction_of_isHallTriple {a b c : Composition n} (h : IsHallTriple a b c) :
    ∃ (N r : ℕ) (P : HallPartition a b c N r), 1 ≤ r ∧ r ≤ n ∧
      atomCoefficient (key a * key b) c =
        ((∏ s, P.blockPolynomial s tVar) *
          ∏ ij ∈ P.pairs, (1 - single (Pi.single ij.2 1 - Pi.single ij.1 1) 1 : Laurent P.m)).coeff
          (fun _ => 1) := by
  obtain ⟨N, r, hr, hrn, ⟨P⟩⟩ := h
  exact ⟨N, r, P, hr, hrn, paired_reduction P⟩

end

end Schubert.RS.Hall
