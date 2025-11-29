import MIL.Common
import Mathlib.Topology.Instances.Real.Lemmas

open Set Filter Topology

lemma Tendsto_goal (f : ℝ -> ℝ) (F : Filter ℝ) (G : Filter ℝ)
: (∀delta ∈ G, ∃ epsilon ∈ F, ∀ h ∈ epsilon, f h ∈ delta) -> Tendsto f F G := by
  intro hf
  simp [Filter.Tendsto, Filter.map, Filter.instPartialOrder]
  intro U hU
  simp [preimage]
  rcases hf U hU with ⟨a, b, c⟩
  exact mem_of_superset b c

lemma Tendsto_term {f : ℝ -> ℝ} {F : Filter ℝ} {G : Filter ℝ}
: Tendsto f F G -> ∀delta ∈ G, ∃ epsilon ∈ F, ∀ h ∈ epsilon, f h ∈ delta := by
  intro ht delta hdelta
  simp [Filter.Tendsto, Filter.map, Filter.instPartialOrder] at ht
  use f ⁻¹' delta
  simp [ht hdelta]

lemma c1_to_c0 (g : ℝ -> ℝ) (x : ℝ) (g'x : ℝ) (hg : Tendsto (fun h : ℝ => if h = 0 then g'x else (g (x + h) - g x) / h) (𝓝 0) (𝓝 g'x))
: Tendsto (fun h => g (x + h) - g x) (𝓝 0) (𝓝 0) := by
  have hh : Tendsto (fun h => h) (𝓝 (0 : ℝ)) (𝓝 0) := by
    exact fun ⦃U⦄ a => a
  have h₁ := Tendsto.mul hh hg
  have hh₁ : (fun x_1 => x_1 * if x_1 = 0 then g'x else (g (x + x_1) - g x) / x_1) = (fun h => g (x + h) - g x) := by
    ext h
    by_cases h₀ : h = 0
    · simp [h₀]
    · simp [h₀]
      exact mul_div_cancel₀ (g (x + h) - g x) h₀
  rw [hh₁] at h₁
  convert h₁
  linarith

theorem chain_rule (f : ℝ -> ℝ) (g : ℝ -> ℝ) (x : ℝ)
  (f'gx : ℝ) (hf : Tendsto (fun h : ℝ => if h = 0 then f'gx else (f (g x + h) - f (g x)) / h) (𝓝 0) (𝓝 f'gx))
  (g'x : ℝ) (hg : Tendsto (fun h : ℝ => if h = 0 then g'x else (g (x + h) - g x) / h) (𝓝 0) (𝓝 g'x))
: Tendsto (fun h : ℝ => if h = 0 then f'gx * g'x else (f (g (x + h)) - f (g x)) / h) (𝓝 0) (𝓝 (f'gx * g'x)) := by
  -- refine ((Tendsto_iff _ _ _).2 _)
  let f'g := (fun h : ℝ => if (g (x + h) = g x) then f'gx else (f (g (x + h)) - f (g x)) / (g (x + h) - g x))
  have hfd : Tendsto (fun h : ℝ => if (g (x + h) = g x) then f'gx else (f (g (x + h)) - f (g x)) / (g (x + h) - g x)) (𝓝 0) (𝓝 f'gx) := by
    apply Tendsto_goal
    intro del hdel
    have ⟨t, tdel, topen, tf'gx⟩ := mem_nhds_iff.mp hdel
    have gcont := Tendsto_term (c1_to_c0 g x g'x hg)
    have ⟨eps, eps₀, leps⟩ := Tendsto_term hf del hdel
    have t₀ : ((fun x => x - f'gx) '' t) ∈ 𝓝 0 :=
      mem_nhds_iff.mpr ⟨(fun x => x - f'gx) '' t, (by rfl), (isOpenMap_sub_right f'gx t topen), (by
        simp
        use f'gx, tf'gx
        linarith
      )⟩
    have ⟨zeta, zeta₀, hzeta⟩ := gcont eps eps₀
    use zeta, zeta₀ -- This one is still variable
    intro z zeps
    by_cases g₀ : g (x + z) = g x
    · simp [g₀]
      exact mem_of_mem_nhds hdel
    · simp [g₀]
      have h₂ := leps (g (x + z) - g x) (hzeta z zeps)
      have g₁ : g (x + z) - g x ≠ 0 := fun _ => g₀ (by linarith)
      simp [g₁] at h₂
      exact h₂

  have h₁ : (fun h => if h = 0 then f'gx * g'x else (f (g (x + h)) - f (g x)) / h) = (fun h =>
    (if g (x + h) = g x then f'gx else (f (g (x + h)) - f (g x)) / (g (x + h) - g x)) * (if h = 0 then g'x else (g (x + h) - g x) / h)) := by
    ext h
    by_cases h₀ : h = 0
    · simp [h₀]
    by_cases g₀ : g (x + h) = g x
    · simp [g₀]
    · simp [g₀, h₀]
      have g₁ : g (x + h) - g x ≠ 0 := fun _ => g₀ (by linarith)
      field_simp

  rw [h₁]
  exact Tendsto.mul hfd hg
