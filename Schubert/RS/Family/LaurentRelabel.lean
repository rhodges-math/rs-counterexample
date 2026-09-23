import Schubert.RS.Laurent

/-! Relabeling Laurent variables preserves the coefficient with every exponent
equal to one. This makes all target-order conventions explicit. -/

namespace Schubert.RS.Family
noncomputable section
variable {n k : ℕ}

def weightRelabel (e : Fin n ≃ Fin k) : Weight n ≃+ Weight k where
  toFun w j := w (e.symm j)
  invFun w i := w (e i)
  left_inv w := by funext i; simp
  right_inv w := by funext j; simp
  map_add' _ _ := rfl

def laurentRelabel (e : Fin n ≃ Fin k) : Laurent n ≃+* Laurent k :=
  AddMonoidAlgebra.mapDomainRingEquiv ℤ (weightRelabel e)

@[simp] theorem laurentRelabel_single (e : Fin n ≃ Fin k) (w : Weight n) (a : ℤ) :
    laurentRelabel e (AddMonoidAlgebra.single w a) =
      AddMonoidAlgebra.single (weightRelabel e w) a := by
  exact AddMonoidAlgebra.mapDomainRingEquiv_single _ _ _

@[simp] theorem weightRelabel_single (e : Fin n ≃ Fin k) (i : Fin n) (a : ℤ) :
    weightRelabel e (Pi.single i a) = Pi.single (e i) a := by
  funext j
  change (Pi.single i a : Weight n) (e.symm j) = (Pi.single (e i) a : Weight k) j
  by_cases h : j=e i
  · subst j; simp
  · have h' : e.symm j ≠ i := by intro he; apply h; simpa using congrArg e he
    simp [h,h']

theorem laurentRelabel_coefficient (e : Fin n ≃ Fin k) (f : Laurent n) (w : Weight k) :
    (laurentRelabel e f).coeff w = f.coeff (fun i => w (e i)) := by
  simp [laurentRelabel,AddMonoidAlgebra.coeff_mapDomainRingEquiv,weightRelabel]

@[simp] theorem laurentRelabel_coefficient_one (e : Fin n ≃ Fin k) (f : Laurent n) :
    (laurentRelabel e f).coeff (fun _ => 1) = f.coeff (fun _ => 1) :=
  laurentRelabel_coefficient e f _

end
end Schubert.RS.Family
