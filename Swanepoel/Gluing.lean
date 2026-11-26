module
public import Swanepoel.Arithmetic
@[expose] public section

noncomputable section
namespace Swanepoel

theorem extremal_disjoint (a b : ℕ) :
    extremalValue a + extremalValue b ≤ extremalValue (a+b) := by
  have ha := Real.sq_sqrt (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  have hb := Real.sq_sqrt (Nat.cast_nonneg b : (0 : ℝ) ≤ b)
  have hc := Real.sq_sqrt (Nat.cast_nonneg (a+b) : (0 : ℝ) ≤ (a+b : ℕ))
  have hsa := Real.sqrt_nonneg (a : ℝ)
  have hsb := Real.sqrt_nonneg (b : ℝ)
  have hsc := Real.sqrt_nonneg ((a+b : ℕ) : ℝ)
  have hroot : Real.sqrt ((a+b : ℕ) : ℝ) ≤ Real.sqrt a + Real.sqrt b := by
    push_cast at hc hsc ⊢
    nlinarith [mul_nonneg hsa hsb]
  unfold extremalValue
  apply Int.le_floor.mpr
  simp only [Int.cast_add, Nat.cast_add]
  have hfa := Int.floor_le (2*(a : ℝ)-2*Real.sqrt a)
  have hfb := Int.floor_le (2*(b : ℝ)-2*Real.sqrt b)
  push_cast at hroot
  linarith

theorem extremal_one_vertex (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : c+1 = a+b) : extremalValue a + extremalValue b ≤ extremalValue c := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hcR : (c : ℝ)+1 = (a : ℝ)+b := by exact_mod_cast hc
  have hsa : 1 ≤ Real.sqrt (a : ℝ) := Real.one_le_sqrt.mpr haR
  have hsb : 1 ≤ Real.sqrt (b : ℝ) := Real.one_le_sqrt.mpr hbR
  have hsc := Real.sqrt_nonneg (c : ℝ)
  have hqa := Real.sq_sqrt (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  have hqb := Real.sq_sqrt (Nat.cast_nonneg b : (0 : ℝ) ≤ b)
  have hqc := Real.sq_sqrt (Nat.cast_nonneg c : (0 : ℝ) ≤ c)
  have hroot : 1+Real.sqrt (c : ℝ) ≤ Real.sqrt a+Real.sqrt b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsa) (sub_nonneg.mpr hsb)]
  unfold extremalValue
  apply Int.le_floor.mpr
  simp only [Int.cast_add]
  have hfa := Int.floor_le (2*(a : ℝ)-2*Real.sqrt a)
  have hfb := Int.floor_le (2*(b : ℝ)-2*Real.sqrt b)
  linarith

end Swanepoel
