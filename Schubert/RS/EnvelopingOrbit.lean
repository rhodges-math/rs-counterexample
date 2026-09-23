import Schubert.RS.Representation.CyclicGeneration

namespace Schubert.RS.Representation
noncomputable section

variable {n : ℕ} {X : Type*} [AddCommGroup X] [Module ℂ X]
  (ρ : Enveloping n →ₐ[ℂ] Module.End ℂ X) (z : X)

def envelopingOrbitMap : Enveloping n →ₗ[ℂ] X where
  toFun a := ρ a z
  map_add' a b := by rw [map_add,LinearMap.add_apply]
  map_smul' c a := by rw [map_smul]; rfl

def envelopingOrbit : Submodule ℂ X := (envelopingOrbitMap ρ z).range

theorem envelopingOrbit_generator : z∈envelopingOrbit ρ z :=
  ⟨1,by simp [envelopingOrbitMap]⟩

theorem envelopingOrbit_stable (a : Enveloping n) {x : X} (hx : x∈envelopingOrbit ρ z) :
    ρ a x∈envelopingOrbit ρ z := by
  obtain ⟨b,rfl⟩ := hx
  exact ⟨a*b,by simp [envelopingOrbitMap,map_mul]⟩

theorem enveloping_stable (Y : Submodule ℂ X)
    (hY : ∀ A x, x∈Y → ρ (UniversalEnvelopingAlgebra.ι ℂ A) x∈Y)
    (a : Enveloping n) {x : X} (hx : x∈Y) : ρ a x∈Y := by
  induction a using enveloping_induction generalizing x with
  | hC c => simpa using Y.smul_mem c hx
  | hι A => exact hY A x hx
  | hmul a b ha hb =>
    rw [map_mul]
    exact ha (hb hx)
  | hadd a b ha hb =>
    rw [map_add,LinearMap.add_apply]
    exact Y.add_mem (ha hx) (hb hx)

theorem envelopingOrbit_le (Y : Submodule ℂ X) (hz : z∈Y)
    (hY : ∀ A x, x∈Y → ρ (UniversalEnvelopingAlgebra.ι ℂ A) x∈Y) :
    envelopingOrbit ρ z≤Y := by
  rintro x ⟨a,rfl⟩
  exact enveloping_stable ρ Y hY a hz

end
end Schubert.RS.Representation
