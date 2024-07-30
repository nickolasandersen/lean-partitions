import Mathlib

theorem primitive_root {p : ℕ} [pp : Fact p.Prime] : ∃ g : (ZMod p)ˣ, ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g := by
  have dom : IsDomain (ZMod p) := ZMod.instIsDomain p
  have cyc : IsCyclic (ZMod p)ˣ := instIsCyclicUnitsOfFinite
  obtain ⟨g, hg⟩ := cyc
  exact ⟨g, hg⟩
