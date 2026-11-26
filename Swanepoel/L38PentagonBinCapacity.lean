module
public import Swanepoel.UnitCircleSharpIntervals
public import Swanepoel.PentagonCrossingCones
@[expose] public section

noncomputable section
namespace Swanepoel
open scoped BigOperators

def l38BankBin (i : Fin 5) : Fin 5 := ![0,4,3,2,0] i

def l38PositiveBin (a b : Fin 5) : Prop :=
  (b.val : ℤ)-a.val=1 ∨ (b.val : ℤ)-a.val=2 ∨ (b.val : ℤ)-a.val= -4

def l38NegativeBin (a b : Fin 5) : Prop :=
  (b.val : ℤ)-a.val= -2 ∨ (b.val : ℤ)-a.val= -1 ∨ (b.val : ℤ)-a.val=4

instance (a b : Fin 5) : Decidable (l38PositiveBin a b) :=
  inferInstanceAs (Decidable ((b.val : ℤ)-a.val=1 ∨ (b.val : ℤ)-a.val=2 ∨ (b.val : ℤ)-a.val= -4))

instance (a b : Fin 5) : Decidable (l38NegativeBin a b) :=
  inferInstanceAs (Decidable ((b.val : ℤ)-a.val= -2 ∨ (b.val : ℤ)-a.val= -1 ∨ (b.val : ℤ)-a.val=4))

theorem l38_positive_sharp_bin (ρ a b : ℝ) (i j : Fin 5)
    (ha : (i.val : ℝ)< a ∧ a< i.val+1) (hb : (j.val : ℝ)< b ∧ b< j.val+1)
    (hcone : Real.sqrt 3/2 < inner ℝ (unitAngleVector (ρ+a+3/2)) (unitAngleVector (ρ+b))) :
    l38PositiveBin i j := by
  have ha0 : 0< a := lt_of_le_of_lt (Nat.cast_nonneg _) ha.1
  have hb0 : 0< b := lt_of_le_of_lt (Nat.cast_nonneg _) hb.1
  have ha5 : a<5 := by
    have h : (i.val : ℝ)≤4 := by exact_mod_cast (by omega : i.val≤4)
    linarith only [h,ha.2]
  have hb5 : b<5 := by
    have h : (j.val : ℝ)≤4 := by exact_mod_cast (by omega : j.val≤4)
    linarith only [h,hb.2]
  by_cases hlow : -11/2≤ b-a-3/2
  · have hi := positive_sharp_phase_interval ρ a b (by
      rw [abs_le]
      constructor
      · linarith only [hlow]
      · linarith only [ha0,hb5]) hcone
    have h1 : i.val< j.val := by
      have h : (i.val : ℝ)< j.val := by linarith only [hi.1,ha.1,hb.2]
      exact_mod_cast h
    have h2 : j.val< i.val+3 := by
      have h : (j.val : ℝ)< i.val+3 := by linarith only [hi.2,ha.2,hb.1]
      exact_mod_cast h
    unfold l38PositiveBin
    omega
  · have h : j.val+3< i.val := by
      have hh : (j.val : ℝ)+3< i.val := by linarith only [ha.2,hb.1,lt_of_not_ge hlow]
      exact_mod_cast hh
    unfold l38PositiveBin
    omega

theorem l38_negative_sharp_bin (ρ a b : ℝ) (i j : Fin 5)
    (ha : (i.val : ℝ)< a ∧ a< i.val+1) (hb : (j.val : ℝ)< b ∧ b< j.val+1)
    (hcone : inner ℝ (unitAngleVector (ρ+a+3/2)) (unitAngleVector (ρ+b))< -Real.sqrt 3/2) :
    l38NegativeBin i j := by
  have ha0 : 0< a := lt_of_le_of_lt (Nat.cast_nonneg _) ha.1
  have hb0 : 0< b := lt_of_le_of_lt (Nat.cast_nonneg _) hb.1
  have ha5 : a<5 := by
    have h : (i.val : ℝ)≤4 := by exact_mod_cast (by omega : i.val≤4)
    linarith only [h,ha.2]
  have hb5 : b<5 := by
    have h : (j.val : ℝ)≤4 := by exact_mod_cast (by omega : j.val≤4)
    linarith only [h,hb.2]
  have hcos : Real.sqrt 3/2< Real.cos (Real.pi/3*(b-a+3/2)) := by
    rw [unitAngleVector_inner] at hcone
    rw [show Real.pi/3*(b-a+3/2)=Real.pi/3*((ρ+b)-(ρ+a+3/2))+Real.pi by ring,
      Real.cos_add_pi]
    linarith only [hcone]
  by_cases hhi : b-a+3/2≤11/2
  · have hh := abs_lt.mp (cos_sharp_phase_abs_lt_half (b-a+3/2) (by
      rw [abs_le]
      constructor
      · linarith only [ha5,hb0]
      · exact hhi) hcos)
    have h1 : j.val< i.val := by
      have h : (j.val : ℝ)< i.val := by linarith only [hh.2,ha.2,hb.1]
      exact_mod_cast h
    have h2 : i.val< j.val+3 := by
      have h : (i.val : ℝ)< j.val+3 := by linarith only [hh.1,ha.1,hb.2]
      exact_mod_cast h
    unfold l38NegativeBin
    omega
  · have h : i.val+3< j.val := by
      have hh : (i.val : ℝ)+3< j.val := by linarith only [ha.1,hb.2,lt_of_not_ge hhi]
      exact_mod_cast hh
    unfold l38NegativeBin
    omega

def l38SingleBin (sector bin : Fin 5) : Prop :=
  l38PositiveBin (l38BankBin (sector+4)) bin ∨ l38NegativeBin (l38BankBin sector) bin

def l38DoubleBin (sector bin : Fin 5) : Prop :=
  (l38PositiveBin (l38BankBin (sector+4)) bin ∧ l38PositiveBin (l38BankBin (sector+3)) bin) ∨
  (l38NegativeBin (l38BankBin sector) bin ∧ l38NegativeBin (l38BankBin (sector+1)) bin)

instance (sector bin : Fin 5) : Decidable (l38SingleBin sector bin) :=
  inferInstanceAs (Decidable (l38PositiveBin (l38BankBin (sector+4)) bin ∨ l38NegativeBin (l38BankBin sector) bin))

instance (sector bin : Fin 5) : Decidable (l38DoubleBin sector bin) :=
  inferInstanceAs (Decidable ((l38PositiveBin (l38BankBin (sector+4)) bin ∧ l38PositiveBin (l38BankBin (sector+3)) bin) ∨
    (l38NegativeBin (l38BankBin sector) bin ∧ l38NegativeBin (l38BankBin (sector+1)) bin)))

def l38BinCapacity (sector bin : Fin 5) : ℕ :=
  if l38DoubleBin sector bin then 2 else if l38SingleBin sector bin then 1 else 0

theorem l38_bin_capacity_sum_le_three :
    ∀ sector : Fin 5,(∑ i : Fin 5,l38BinCapacity sector (l38BankBin i))≤3 := by
  decide

theorem l38_degree_le_bin_capacity (sector bin : Fin 5) (k : ℕ) (hk : k≤2)
    (hs : 0< k → l38SingleBin sector bin) (hd : k=2 → l38DoubleBin sector bin) :
    k≤ l38BinCapacity sector bin := by
  unfold l38BinCapacity
  split_ifs with hdouble hsingle
  · exact hk
  · have hne : k≠2 := fun h => hdouble (hd h)
    omega
  · have hz : k=0 := by
      by_contra hn
      exact hsingle (hs (by omega))
    omega

namespace PentagonFaceBoundary
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} (P : PentagonFaceBoundary G F)

structure BankBinData (ρ : ℝ) where
  angle : Fin 5→ℝ
  bounds : ∀ i,(l38BankBin i).val< angle i ∧ angle i<(l38BankBin i).val+1
  phase : ∀ i,unitAngleVector (ρ+angle i)=P.normal i

theorem BankBinData.positive_bin {ρ : ℝ} (D : P.BankBinData ρ)
    (i bin : Fin 5) (θ : ℝ) (hθ : (bin.val : ℝ)< θ ∧ θ< bin.val+1)
    (h : Real.sqrt 3/2 < inner ℝ (carriedVector (P.dart i)) (unitAngleVector (ρ+θ))) :
    l38PositiveBin (l38BankBin i) bin := by
  rw [carriedVector_phase (P.dart i) (ρ+D.angle i) (D.phase i)] at h
  exact l38_positive_sharp_bin ρ (D.angle i) θ (l38BankBin i) bin (D.bounds i) hθ h

theorem BankBinData.negative_bin {ρ : ℝ} (D : P.BankBinData ρ)
    (i bin : Fin 5) (θ : ℝ) (hθ : (bin.val : ℝ)< θ ∧ θ< bin.val+1)
    (h : inner ℝ (carriedVector (P.dart i)) (unitAngleVector (ρ+θ))< -Real.sqrt 3/2) :
    l38NegativeBin (l38BankBin i) bin := by
  rw [carriedVector_phase (P.dart i) (ρ+D.angle i) (D.phase i)] at h
  exact l38_negative_sharp_bin ρ (D.angle i) θ (l38BankBin i) bin (D.bounds i) hθ h

theorem BankBinData.single_bin {ρ : ℝ} (D : P.BankBinData ρ)
    (sector bin : Fin 5) (θ : ℝ) (hθ : (bin.val : ℝ)< θ ∧ θ< bin.val+1)
    (h : P.SingleSectorCone (unitAngleVector (ρ+θ)) sector) : l38SingleBin sector bin := by
  rcases h with h | h
  · exact Or.inl (D.positive_bin P (sector+4) bin θ hθ h)
  · exact Or.inr (D.negative_bin P sector bin θ hθ h)

theorem BankBinData.double_bin {ρ : ℝ} (D : P.BankBinData ρ)
    (sector bin : Fin 5) (θ : ℝ) (hθ : (bin.val : ℝ)< θ ∧ θ< bin.val+1)
    (h : P.DoubleSectorCone (unitAngleVector (ρ+θ)) sector) : l38DoubleBin sector bin := by
  rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl ⟨D.positive_bin P (sector+4) bin θ hθ h1,D.positive_bin P (sector+3) bin θ hθ h2⟩
  · exact Or.inr ⟨D.negative_bin P sector bin θ hθ h1,D.negative_bin P (sector+1) bin θ hθ h2⟩

end PentagonFaceBoundary
end Swanepoel
