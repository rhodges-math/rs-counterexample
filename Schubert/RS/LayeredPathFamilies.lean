import Schubert.RS.FirstPathIntersection
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi

/-! Matched finite path families and their first-intersection sign reversal.
This implements the cancellation step of the Hall determinant proof.
Identifying the planar nonintersecting survivors is a separate step. -/

namespace Schubert.RS
noncomputable section
variable {V : Type*} {d T : ℕ}

@[ext] structure LayeredPathFamily (E : Fin T → V → V → Prop)
    (s f : Fin d → V) where
  matching : Equiv.Perm (Fin d)
  path : Fin d → Fin (T + 1) → V
  start : ∀ i, path i 0 = s i
  finish : ∀ i, path i (Fin.last T) = f (matching i)
  edges : ∀ i k, E k (path i k.castSucc) (path i k.succ)

variable {E : Fin T → V → V → Prop} {s f : Fin d → V}

instance [Finite V] : Finite (LayeredPathFamily E s f) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  exact Finite.of_injective (fun P : LayeredPathFamily E s f => (P.matching, P.path)) (by
    intro P Q h
    apply LayeredPathFamily.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h)

instance [Fintype V] : Fintype (LayeredPathFamily E s f) := Fintype.ofFinite _

theorem firstIntersection_lt_finish (P : LayeredPathFamily E s f)
    (hf : Function.Injective f) (hp : (pathCollisionTimes P.path).Nonempty) :
    firstPathIntersection P.path hp < Fin.last T := by
  have h := firstPathPair_spec P.path hp
  apply lt_of_le_of_ne (Fin.le_last _)
  intro he
  rw [he, P.finish, P.finish] at h
  exact (ne_of_lt h.1) (P.matching.injective (hf h.2))

/-- Exchange the chosen tails and compose the endpoint matching with their
transposition. The source labels themselves remain fixed. -/
def exchangePathFamily (P : LayeredPathFamily E s f)
    (hf : Function.Injective f) (hp : (pathCollisionTimes P.path).Nonempty) :
    LayeredPathFamily E s f where
  matching := P.matching * Equiv.swap
    (ofLex (firstPathPair P.path hp)).1 (ofLex (firstPathPair P.path hp)).2
  path := exchangeFirstPathTails P.path hp
  start i := by
    simp only [exchangeFirstPathTails, swapPathTails, Fin.zero_le, if_true]
    exact P.start i
  finish i := by
    have ht := firstIntersection_lt_finish P hf hp
    simp only [exchangeFirstPathTails, swapPathTails, not_le.mpr ht, if_false]
    exact P.finish _
  edges := swapPathTails_edges P.path _ _ _ (firstPathPair_spec P.path hp).2 E P.edges

theorem exchangePathFamily_nonempty (P : LayeredPathFamily E s f)
    (hf : Function.Injective f) (hp : (pathCollisionTimes P.path).Nonempty) :
    (pathCollisionTimes (exchangePathFamily P hf hp).path).Nonempty :=
  exchangeFirstPathTails_nonempty P.path hp

theorem exchangePathFamily_involutive (P : LayeredPathFamily E s f)
    (hf : Function.Injective f) (hp : (pathCollisionTimes P.path).Nonempty) :
    exchangePathFamily (exchangePathFamily P hf hp) hf
      (exchangePathFamily_nonempty P hf hp) = P := by
  apply LayeredPathFamily.ext
  · change (P.matching * Equiv.swap _ _) *
      Equiv.swap (ofLex (firstPathPair (exchangeFirstPathTails P.path hp) _)).1
        (ofLex (firstPathPair (exchangeFirstPathTails P.path hp) _)).2 = P.matching
    simp only [exchangeFirstPathTails, firstPathPair_swap]
    simp [mul_assoc]
  · exact exchangeFirstPathTails_involutive P.path hp

def pathFamilyWeight {R : Type*} [CommRing R] (w : Fin T → V → V → R)
    (P : LayeredPathFamily E s f) : R :=
  (P.matching.sign : ℤ) • ∏ k, ∏ i, w k (P.path i k.castSucc) (P.path i k.succ)

theorem exchangePathFamily_weight {R : Type*} [CommRing R]
    (w : Fin T → V → V → R) (P : LayeredPathFamily E s f)
    (hf : Function.Injective f) (hp : (pathCollisionTimes P.path).Nonempty) :
    pathFamilyWeight w (exchangePathFamily P hf hp) = -pathFamilyWeight w P := by
  have hne := ne_of_lt (firstPathPair_spec P.path hp).1
  change (((P.matching * Equiv.swap _ _).sign : ℤˣ) : ℤ) •
    (∏ k, ∏ i, w k (exchangeFirstPathTails P.path hp i k.castSucc)
      (exchangeFirstPathTails P.path hp i k.succ)) = _
  rw [exchangeFirstPathTails_weight, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne]
  simp [pathFamilyWeight]

theorem exchangePathFamily_ne (P : LayeredPathFamily E s f)
    (hf : Function.Injective f) (hp : (pathCollisionTimes P.path).Nonempty) :
    exchangePathFamily P hf hp ≠ P := by
  intro h
  have hm := congrArg LayeredPathFamily.matching h
  change P.matching * Equiv.swap (ofLex (firstPathPair P.path hp)).1
    (ofLex (firstPathPair P.path hp)).2 = P.matching at hm
  have hs : Equiv.swap (ofLex (firstPathPair P.path hp)).1
      (ofLex (firstPathPair P.path hp)).2 = 1 :=
    mul_left_cancel (hm.trans (mul_one P.matching).symm)
  have hv := congrArg (fun e : Equiv.Perm (Fin d) => e (ofLex (firstPathPair P.path hp)).1) hs
  have he : (ofLex (firstPathPair P.path hp)).2 = (ofLex (firstPathPair P.path hp)).1 := by
    simpa using hv
  exact (ne_of_lt (firstPathPair_spec P.path hp).1) he.symm

/-- The entire intersecting part of the determinant's signed path sum
cancels, with no division by two and over any commutative ring. -/
theorem intersecting_path_family_sum [Fintype V] {R : Type*} [CommRing R]
    (w : Fin T → V → V → R) (hf : Function.Injective f) :
    ∑ P : {P : LayeredPathFamily E s f // (pathCollisionTimes P.path).Nonempty},
      pathFamilyWeight w P.val = 0 := by
  classical
  let g (P : {P : LayeredPathFamily E s f // (pathCollisionTimes P.path).Nonempty}) :=
    (⟨exchangePathFamily P.val hf P.property,
      exchangePathFamily_nonempty P.val hf P.property⟩ :
      {P : LayeredPathFamily E s f // (pathCollisionTimes P.path).Nonempty})
  apply Finset.sum_involution (fun P _ => g P)
  · intro P _
    change pathFamilyWeight w P.val + pathFamilyWeight w (exchangePathFamily P.val hf P.property) = 0
    rw [exchangePathFamily_weight, add_neg_cancel]
  · intro P _ _ he
    exact exchangePathFamily_ne P.val hf P.property (congrArg Subtype.val he)
  · intro P _
    exact Finset.mem_univ _
  · intro P _
    apply Subtype.ext
    exact exchangePathFamily_involutive P.val hf P.property

/-- The signed sum over all matched families equals the sum over all
nonintersecting survivors. The latter's planar matching is not assumed here. -/
theorem path_family_sum_nonintersecting [Fintype V] {R : Type*} [CommRing R]
    (w : Fin T → V → V → R) (hf : Function.Injective f) :
    (∑ P : LayeredPathFamily E s f, pathFamilyWeight w P) =
      ∑ P : {P : LayeredPathFamily E s f // ¬(pathCollisionTimes P.path).Nonempty},
        pathFamilyWeight w P.val := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype
    (fun P : LayeredPathFamily E s f => (pathCollisionTimes P.path).Nonempty)
    (pathFamilyWeight w)
  rw [intersecting_path_family_sum w hf, zero_add] at h
  exact h.symm

end
end Schubert.RS
