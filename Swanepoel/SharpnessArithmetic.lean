module
public import Swanepoel.Definitions
public import Mathlib.Data.Nat.Sqrt
@[expose] public section

noncomputable section
namespace Swanepoel

theorem extremal_square (k : ℕ) :
    extremalValue (k*k) = 2*(k*k : ℕ)-2*(k : ℤ) := by
  unfold extremalValue
  have he : ((k*k : ℕ) : ℝ) = (k : ℝ)^2 := by push_cast; ring
  rw [he, Real.sqrt_sq (Nat.cast_nonneg k)]
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor <;> nlinarith

theorem extremal_lower_band (k r : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (hrk : r ≤ k) :
    extremalValue (k*k+r) = 2*(k*k+r : ℕ)-2*(k : ℤ)-1 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrkR : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ)^2+r by positivity)
  have hs0 := Real.sqrt_nonneg ((k : ℝ)^2+r)
  have hlo : (k : ℝ) < Real.sqrt ((k : ℝ)^2+r) := by nlinarith
  have hhi : Real.sqrt ((k : ℝ)^2+r) < (k : ℝ)+1/2 := by nlinarith
  unfold extremalValue
  have he : ((k*k+r : ℕ) : ℝ) = (k : ℝ)^2+r := by push_cast; ring
  rw [he]
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor <;> nlinarith

theorem extremal_upper_band (k r : ℕ) (hk : 1 ≤ k) (hkr : k < r) (hr : r ≤ 2*k) :
    extremalValue (k*k+r) = 2*(k*k+r : ℕ)-2*(k : ℤ)-2 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkrR : (k : ℝ)+1 ≤ r := by exact_mod_cast (show k+1 ≤ r by omega)
  have hrR : (r : ℝ) ≤ 2*k := by exact_mod_cast hr
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (k : ℝ)^2+r by positivity)
  have hs0 := Real.sqrt_nonneg ((k : ℝ)^2+r)
  have hlo : (k : ℝ)+1/2 < Real.sqrt ((k : ℝ)^2+r) := by nlinarith
  have hhi : Real.sqrt ((k : ℝ)^2+r) < (k : ℝ)+1 := by nlinarith
  unfold extremalValue
  have he : ((k*k+r : ℕ) : ℝ) = (k : ℝ)^2+r := by push_cast; ring
  rw [he]
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor <;> nlinarith

theorem grid_edges_int (w h r : ℕ) (hw : 1 ≤ w) (hh : 1 ≤ h) :
    (((w-1)*h+(r-1)+(w*(h-1)+r) : ℕ) : ℤ) =
      2*(w*h+r : ℕ)-(w : ℤ)-h-(if r=0 then 0 else 1) := by
  by_cases hr : r=0
  · subst r
    simp only [Nat.zero_sub, Nat.add_zero, Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub hw, Nat.cast_sub hh, Nat.cast_one, ite_true]
    ring
  · have hr1 : 1 ≤ r := by omega
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hw, Nat.cast_sub hh,
      Nat.cast_sub hr1, Nat.cast_one, hr, ite_false]
    ring

theorem sharp_grid_parameters (n : ℕ) (hn : 1 ≤ n) :
    ∃ w h r : ℕ, 1 ≤ w ∧ 1 ≤ h ∧ r ≤ w ∧ w*h+r=n ∧
      (((w-1)*h+(r-1)+(w*(h-1)+r) : ℕ) : ℤ) = extremalValue n := by
  let k := Nat.sqrt n
  let r := n-k*k
  have hk : 1 ≤ k := Nat.sqrt_pos.mpr hn
  have hkn : k*k ≤ n := Nat.sqrt_le n
  have he : k*k+r=n := Nat.add_sub_of_le hkn
  have hr : r ≤ 2*k := by have h := Nat.sqrt_le_add n; dsimp [k, r] at *; omega
  by_cases hrk : r ≤ k
  · refine ⟨k,k,r,hk,hk,hrk,he,?_⟩
    rw [grid_edges_int _ _ _ hk hk, he]
    by_cases hr0 : r=0
    · have hn0 : n=k*k := by omega
      rw [hn0, hr0, ite_eq_left (rfl : (0 : ℕ)=0), extremal_square]
      ring
    · have ht := extremal_lower_band k r hk (by omega) hrk
      rw [he] at ht
      rw [ht, ite_eq_right hr0]
      ring
  · have hrt : 1 ≤ r-k := by omega
    have htw : r-k ≤ k+1 := by omega
    have hen : (k+1)*k+(r-k)=n := by
      have hh := Nat.sub_add_cancel (show k ≤ r by omega)
      nlinarith [he]
    refine ⟨k+1,k,r-k,by omega,hk,htw,hen,?_⟩
    rw [grid_edges_int _ _ _ (by omega) hk, hen,
      ite_eq_right (show r-k ≠ 0 by omega)]
    have ht := extremal_upper_band k r hk (by omega) hr
    rw [he] at ht
    rw [ht]
    push_cast
    ring

end Swanepoel
