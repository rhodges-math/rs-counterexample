import Schubert.RS.JosephPolo.ColumnProducts

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation
open scoped BigOperators

/-- An increasing Bruhat chain realizing the columns, bounded by w.
This is a combinatorial condition, with no independence or spanning built in. -/
def HasFlagDefiningChain {n d : ℕ} (h : Fin d → Fin n)
    (T : (j : Fin d) → FlagMinorRowSet (h j)) (w : FinPermutation n) : Prop :=
  ∃ v : Fin d → FinPermutation n,
    (∀ i j, i ≤ j → v i ≤ᴮ v j) ∧
    (∀ j, flagPrefixRows (v j) (h j) = T j) ∧
    (∀ j, v j ≤ᴮ w)

theorem HasFlagDefiningChain.last {n d : ℕ} {h : Fin (d+1) → Fin n}
    {T : (j : Fin (d+1)) → FlagMinorRowSet (h j)} {w : FinPermutation n}
    (hT : HasFlagDefiningChain h T w) :
    ∃ v : FinPermutation n, v ≤ᴮ w ∧
      flagPrefixRows v (h (Fin.last d)) = T (Fin.last d) ∧
      HasFlagDefiningChain (fun j => h j.castSucc) (fun j => T j.castSucc) v := by
  obtain ⟨v,hmono,hprefix,hbound⟩ := hT
  refine ⟨v (Fin.last d),hbound _,hprefix _,fun j => v j.castSucc,?_,?_,?_⟩
  · intro i j hij
    exact hmono _ _ hij
  · intro j
    exact hprefix j.castSucc
  · intro j
    exact hmono _ _ (Fin.le_last _)

theorem HasFlagDefiningChain.mono {n d : ℕ} {h : Fin d → Fin n}
    {T : (j : Fin d) → FlagMinorRowSet (h j)} {v w : FinPermutation n}
    (hT : HasFlagDefiningChain h T v) (hvw : v ≤ᴮ w) :
    HasFlagDefiningChain h T w := by
  obtain ⟨u,hm,hp,hb⟩ := hT
  exact ⟨u,hm,hp,fun j => strongBruhat_trans (hb j) hvw⟩

theorem HasFlagDefiningChain.of_last {n d : ℕ} {h : Fin (d+1) → Fin n}
    {T : (j : Fin (d+1)) → FlagMinorRowSet (h j)} {v w : FinPermutation n}
    (hvw : v ≤ᴮ w) (hp : flagPrefixRows v (h (Fin.last d)) = T (Fin.last d))
    (hT : HasFlagDefiningChain (fun j => h j.castSucc) (fun j => T j.castSucc) v) :
    HasFlagDefiningChain h T w := by
  obtain ⟨u,hm,hu,hb⟩ := hT
  refine ⟨Fin.snoc u v,?_,?_,?_⟩
  · intro i j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · intro _; simpa using strongBruhat_refl v
      · intro _; simpa using hb i
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · intro hij
        have : ¬ Fin.last d ≤ j.castSucc := by simp
        exact False.elim (this hij)
      · intro hij
        simpa using hm i j hij
  · intro j
    exact Fin.lastCases (by simpa using hp) (fun j => by simpa using hu j) j
  · intro j
    exact Fin.lastCases (by simpa using hvw)
      (fun j => by simpa using strongBruhat_trans (hb j) hvw) j

theorem hasFlagDefiningChain_iff_last {n d : ℕ} {h : Fin (d+1) → Fin n}
    {T : (j : Fin (d+1)) → FlagMinorRowSet (h j)} {w : FinPermutation n} :
    HasFlagDefiningChain h T w ↔
      ∃ v : FinPermutation n, v ≤ᴮ w ∧
        flagPrefixRows v (h (Fin.last d)) = T (Fin.last d) ∧
        HasFlagDefiningChain (fun j => h j.castSucc) (fun j => T j.castSucc) v :=
  ⟨HasFlagDefiningChain.last,fun ⟨_,hb,hp,hT⟩ => hT.of_last hb hp⟩

theorem FlagMinorRowSet.eq_of_rows_eq {n : ℕ} {k : Fin n} {S T : FlagMinorRowSet k}
    (h : ∀ i, S.rows i = T.rows i) : S = T := by
  apply Subtype.ext
  have he : (S.rows : Fin (k.val+1) → Fin n) = T.rows := funext h
  have he' := congrArg (fun f : Fin (k.val+1) → Fin n => Finset.univ.image f) he
  simpa only [FlagMinorRowSet.rows,Finset.image_orderEmbOfFin_univ] using he'

/-- Coordinatewise comparison and the reverse total-sum comparison force
equality. This lets finite minimization select a last column. -/
theorem FlagMinorRowSet.eq_of_le_of_sum_le {n : ℕ} {k : Fin n} {S T : FlagMinorRowSet k}
    (hle : ∀ i, S.rows i ≤ T.rows i)
    (hsum : (∑ i, (T.rows i).val) ≤ ∑ i, (S.rows i).val) : S = T := by
  apply FlagMinorRowSet.eq_of_rows_eq
  intro i
  apply le_antisymm (hle i)
  by_contra hi
  have hlt : (∑ j, (S.rows j).val) < ∑ j, (T.rows j).val :=
    Finset.sum_lt_sum (fun j _ => hle j) ⟨i,Finset.mem_univ _,lt_of_not_ge hi⟩
  exact (not_lt_of_ge hsum) hlt

end
end Schubert.RS.Representation
