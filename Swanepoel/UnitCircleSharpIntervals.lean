module
public import Swanepoel.UnitCirclePhases
@[expose] public section

noncomputable section
namespace Swanepoel

theorem cos_sharp_phase_abs_lt_half (d : ℝ) (hd : |d|≤11/2)
    (hcos : Real.sqrt 3/2<Real.cos (Real.pi/3*d)) : |d|<1/2 := by
  have hp : 0<Real.pi/3 := div_pos Real.pi_pos (by norm_num)
  have heven : Real.cos (Real.pi/3*|d|)=Real.cos (Real.pi/3*d) := by
    rcases le_total 0 d with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,show Real.pi/3*(-d)= -(Real.pi/3*d) by ring,Real.cos_neg]
  by_contra hn
  have hlo : (1/2:ℝ)≤|d| := le_of_not_gt hn
  by_cases hthree : |d|≤3
  · have hbound := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0≤Real.pi/6 by positivity)
      (show Real.pi/3*|d|≤Real.pi by nlinarith only [hp,hthree])
      (show Real.pi/6≤Real.pi/3*|d| by nlinarith only [hp,hlo])
    rw [Real.cos_pi_div_six,heven] at hbound
    linarith only [hcos,hbound]
  · have hbound := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0≤Real.pi/6 by positivity)
      (show Real.pi/3*(6-|d|)≤Real.pi by nlinarith only [hp,lt_of_not_ge hthree])
      (show Real.pi/6≤Real.pi/3*(6-|d|) by nlinarith only [hp,hd])
    rw [Real.cos_pi_div_six,show Real.pi/3*(6-|d|)=2*Real.pi-Real.pi/3*|d| by ring,
      Real.cos_two_pi_sub,heven] at hbound
    linarith only [hcos,hbound]

theorem positive_sharp_phase_interval (rho offset θ : ℝ)
    (hwindow : |θ-offset-3/2|≤11/2)
    (hcone : Real.sqrt 3/2 < inner ℝ (unitAngleVector (rho+offset+3/2)) (unitAngleVector (rho+θ))) :
    θ∈Set.Ioo (offset+1) (offset+2) := by
  rw [unitAngleVector_inner,
    show Real.pi/3*((rho+θ)-(rho+offset+3/2))=Real.pi/3*(θ-offset-3/2) by ring] at hcone
  have h := abs_lt.mp (cos_sharp_phase_abs_lt_half (θ-offset-3/2) hwindow hcone)
  constructor <;> linarith only [h.1,h.2]

theorem negative_sharp_phase_interval (rho offset θ : ℝ)
    (hwindow : |θ-offset-9/2|≤11/2)
    (hcone : inner ℝ (unitAngleVector (rho+offset+3/2)) (unitAngleVector (rho+θ))< -Real.sqrt 3/2) :
    θ∈Set.Ioo (offset+4) (offset+5) := by
  rw [unitAngleVector_inner] at hcone
  have hpos : Real.sqrt 3/2<Real.cos (Real.pi/3*(θ-offset-9/2)) := by
    rw [show Real.pi/3*(θ-offset-9/2)=Real.pi/3*((rho+θ)-(rho+offset+3/2))-Real.pi by ring,
      Real.cos_sub_pi]
    linarith only [hcone]
  have h := abs_lt.mp (cos_sharp_phase_abs_lt_half (θ-offset-9/2) hwindow hpos)
  constructor <;> linarith only [h.1,h.2]

theorem quarterTurn_sourceNormal {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) :
    quarterTurn (sourceNormal e)=carriedVector e := by
  ext i
  fin_cases i <;> simp [sourceNormal,quarterTurn]

theorem carriedVector_phase {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) (rho : ℝ)
    (hphase : unitAngleVector rho=sourceNormal e) : carriedVector e=unitAngleVector (rho+3/2) := by
  rw [← quarterTurn_sourceNormal,← hphase,quarterTurn_unitAngleVector]

end Swanepoel
