import Schubert.RS.KeyComplement

/-! # Converting the pairing to the rectangle coefficient

The identity is proved for keys and finite Laurent polynomials. Global
key-atom orthogonality subsequently identifies it with an atom coefficient.
-/

namespace Schubert.RS

noncomputable section
variable {n : ℕ}

theorem keyAtomPairing_symmetric (f g : Polynomial n) :
    keyAtomPairing f g = keyAtomPairing g f := by
  unfold keyAtomPairing
  rw [← constantTerm_reverseNeg (toLaurent f * reverseNeg (toLaurent g) * weylFactor n),
    map_mul, map_mul, reverseNeg_involutive, reverseNeg_weylFactor]
  congr 1
  ring

def rectangleCoefficient (w : ℕ) (c : Composition n) (f : Polynomial n) : ℤ :=
  (toLaurent f * toLaurent (key (fun i => w - c i)) * weylFactor n).coeff
    (fun _ => (w : ℤ))

/-- The exact conversion used after key–atom orthogonality in the manuscript. -/
theorem rectangleCoefficient_eq_pairing (w : ℕ) (c : Composition n)
    (hc : ∀ i, c i ≤ w) (f : Polynomial n) :
    rectangleCoefficient w c f = keyAtomPairing (key (fun i => c i.rev)) f := by
  have hk : toLaurent (key (fun i => w - c i)) =
      rectangleMonomial w * reverseNeg (toLaurent (key (fun i => c i.rev))) := by
    have he : reverseComplement w (fun i => c i.rev) = (fun i => w - c i) := by
      funext i
      simp [reverseComplement]
    have h := key_reverseComplement w (fun i => c i.rev) (fun i => hc i.rev)
    rw [he] at h
    exact h
  rw [rectangleCoefficient, hk, ← keyAtomPairing_symmetric]
  calc
    _ = (rectangleMonomial w *
      (toLaurent f * reverseNeg (toLaurent (key (fun i => c i.rev))) * weylFactor n)).coeff
        (fun _ => (w : ℤ)) := by
          apply congrArg (fun p : Laurent n => p.coeff (fun _ => (w : ℤ)))
          ring
    _ = _ := by
      unfold rectangleMonomial keyAtomPairing constantTerm
      simpa only [add_zero] using laurent_coefficient_shift
        (fun _ : Fin n => (w : ℤ)) 0
        (toLaurent f * reverseNeg (toLaurent (key (fun i => c i.rev))) * weylFactor n)

end
end Schubert.RS
