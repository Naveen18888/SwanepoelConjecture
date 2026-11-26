module
public import Swanepoel.Quantitative
public import Mathlib.Analysis.Real.Pi.Bounds
@[expose] public section

noncomputable section
namespace Swanepoel

theorem sqrt_three_ge_twelve_sevenths : (12/7 : ℝ)≤Real.sqrt 3 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)
  nlinarith [Real.sqrt_nonneg (3 : ℝ)]

theorem small_boundary_quadratic_bound (K B R A : ℝ)
    (hK : 0≤K) (hB : 0≤B) (hR : 0≤R) (hboundary : 5*B≤8*K)
    (harea : Real.sqrt 3/2*R≤A) (hiso : A≤B^2/(4*Real.pi)) :
    10000*R≤2379*K^2 := by
  have hpi : (157/50 : ℝ)≤Real.pi := by linarith [Real.pi_gt_d2]
  have hprod : (157/50 : ℝ)*(12/7)≤Real.pi*Real.sqrt 3 :=
    mul_le_mul hpi sqrt_three_ge_twelve_sevenths (by norm_num) Real.pi_pos.le
  have hcoeff : (1884/175 : ℝ)≤2*Real.pi*Real.sqrt 3 := by linarith
  have hcoeffR := mul_le_mul_of_nonneg_right hcoeff hR
  have hareaScaled := mul_le_mul_of_nonneg_left harea (by positivity : 0≤4*Real.pi)
  have hisoScaled : 4*Real.pi*A≤B^2 := by
    have hi := (le_div_iff₀ (by positivity : (0 : ℝ)<4*Real.pi)).mp hiso
    nlinarith
  have hsq : 25*B^2≤64*K^2 := by
    nlinarith [mul_nonneg (by linarith : 0≤8*K-5*B) (by positivity : 0≤8*K+5*B)]
  nlinarith [sq_nonneg K]

theorem small_boundary_quadratic_bound_int (K B R : ℤ) (A : ℝ)
    (hK : 0≤K) (hB : 0≤B) (hR : 0≤R) (hboundary : 5*B≤8*K)
    (harea : Real.sqrt 3/2*(R : ℝ)≤A)
    (hiso : A≤(B : ℝ)^2/(4*Real.pi)) : 10000*R≤2379*K^2 := by
  have h := small_boundary_quadratic_bound (K : ℝ) (B : ℝ) (R : ℝ) A
    (by exact_mod_cast hK) (by exact_mod_cast hB) (by exact_mod_cast hR)
    (by exact_mod_cast hboundary) harea hiso
  exact_mod_cast h

theorem boundary_ends_bound_without_full_pentagon {ι : Type*}
    (F : Finset ι) (L b : ι→ℕ)
    (hL : ∀ f∈F, 5≤L f) (hb : ∀ f∈F, b f≤L f)
    (hno : ∀ f∈F, L f=5 → b f≠5) :
    (∑ f∈F, (b f : ℤ))≤4*∑ f∈F, ((L f : ℤ)-4) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f hf
  have hlen := hL f hf
  have hends := hb f hf
  by_cases h5 : L f=5
  · have hne := hno f hf h5
    omega
  · omega

theorem large_boundary_exists_full_pentagon {ι : Type*}
    (F : Finset ι) (L b : ι→ℕ) (K B : ℤ)
    (hL : ∀ f∈F, 5≤L f) (hb : ∀ f∈F, b f≤L f)
    (hB : B=∑ f∈F, (b f : ℤ))
    (hK : 2*K=B+∑ f∈F, ((L f : ℤ)-4)) (hlarge : 8*K<5*B) :
    ∃ f∈F, L f=5 ∧ b f=5 := by
  by_contra hnone
  have hno : ∀ f∈F, L f=5 → b f≠5 := by
    intro f hf h5 hb5
    exact hnone ⟨f,hf,h5,hb5⟩
  have hbound := boundary_ends_bound_without_full_pentagon F L b hL hb hno
  rw [← hB] at hbound
  omega

end Swanepoel
