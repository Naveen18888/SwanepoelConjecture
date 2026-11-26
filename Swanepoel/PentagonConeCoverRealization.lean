module
public import Swanepoel.PentagonSectorAngles
public import Swanepoel.UnitCircleSharpIntervals
@[expose] public section

noncomputable section
namespace Swanepoel

namespace PentagonFaceBoundary.SectorAngleData
variable {n : ℕ} {G : PennyGraph n} {F : PlaneFace G} {P : PentagonFaceBoundary G F} {j : Fin 5}
    (D : P.SectorAngleData j)
include D

theorem base_positive_interval (θ : ℝ) (hθ : θ∈Set.Ioc (0:ℝ) 6)
    (hcone : Real.sqrt 3/2 < inner ℝ (carriedVector (P.dart (j+4))) (unitAngleVector (D.rho+θ))) :
    θ∈Set.Ioo (1:ℝ) 2 := by
  have hv := carriedVector_phase (P.dart (j+4)) D.rho D.phase_base
  rw [hv] at hcone
  have h := positive_sharp_phase_interval D.rho 0 θ
    (abs_le.mpr ⟨by linarith only [hθ.1],by linarith only [hθ.2]⟩) (by simpa only [add_zero] using hcone)
  simpa only [zero_add] using h

theorem previous_positive_interval (θ : ℝ) (hθ : θ∈Set.Ioc (0:ℝ) 6)
    (hcone : Real.sqrt 3/2 < inner ℝ (carriedVector (P.dart (j+3))) (unitAngleVector (D.rho+θ))) :
    θ∈Set.Ioo (D.a+1) (D.a+2) := by
  have hv := carriedVector_phase (P.dart (j+3)) (D.rho+D.a) D.phase_prev
  rw [hv] at hcone
  exact positive_sharp_phase_interval D.rho D.a θ
    (abs_le.mpr ⟨by linarith only [hθ.1,D.a_lt_two],by linarith only [hθ.2,D.a_pos]⟩) hcone

theorem next_negative_interval (θ : ℝ) (hθ : θ∈Set.Ioc (0:ℝ) 6)
    (hcone : inner ℝ (carriedVector (P.dart j)) (unitAngleVector (D.rho+θ))< -Real.sqrt 3/2) :
    θ∈Set.Ioo (4-D.g) (5-D.g) := by
  have hv := carriedVector_phase (P.dart j) (D.rho-D.g) D.phase_next
  rw [hv] at hcone
  have h := negative_sharp_phase_interval D.rho (-D.g) θ
    (abs_le.mpr ⟨by linarith only [hθ.1,D.g_pos],by linarith only [hθ.2,D.g_lt_two]⟩)
    (by simpa only [sub_eq_add_neg] using hcone)
  constructor <;> linarith only [h.1,h.2]

theorem next_next_negative_interval (θ : ℝ) (hθ : θ∈Set.Ioc (0:ℝ) 6)
    (hcone : inner ℝ (carriedVector (P.dart (j+1))) (unitAngleVector (D.rho+θ))< -Real.sqrt 3/2) :
    θ∈Set.Ioo (4-D.g-D.b) (5-D.g-D.b) := by
  have hv := carriedVector_phase (P.dart (j+1)) (D.rho-D.g-D.b) D.phase_next_next
  rw [hv] at hcone
  have h := negative_sharp_phase_interval D.rho (-D.g-D.b) θ
    (abs_le.mpr ⟨by linarith only [hθ.1,D.g_pos,D.b_pos],
      by linarith only [hθ.2,D.g_lt_two,D.b_lt_two]⟩)
    (by simpa only [sub_eq_add_neg,add_assoc] using hcone)
  constructor <;> linarith only [h.1,h.2]

theorem single_angles (θ : ℝ) (hθ : θ∈Set.Ioc (0:ℝ) 6)
    (hcone : P.SingleSectorCone (unitAngleVector (D.rho+θ)) j) : pentagonSingleAngles D.g θ := by
  rcases hcone with h | h
  · exact Or.inl (D.base_positive_interval θ hθ h)
  · exact Or.inr (D.next_negative_interval θ hθ h)

theorem double_angles (θ : ℝ) (hθ : θ∈Set.Ioc (0:ℝ) 6)
    (hcone : P.DoubleSectorCone (unitAngleVector (D.rho+θ)) j) : pentagonDoubleAngles D.a D.b D.g θ := by
  rcases hcone with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have hi := D.base_positive_interval θ hθ h1
    have hj := D.previous_positive_interval θ hθ h2
    exact Or.inl ⟨by linarith only [hj.1],hi.2⟩
  · have hi := D.next_negative_interval θ hθ h1
    have hj := D.next_next_negative_interval θ hθ h2
    exact Or.inr ⟨hi.1,hj.2⟩

theorem exists_covering_axes :
    ∃ axis : Bool→Plane,(∀ c,‖axis c‖=1) ∧ |inner ℝ (axis false) (axis true)|≤1/2 ∧
      ∀ (normal : Plane),‖normal‖=1 → ∀ k : ℕ,k≤2 →
        (0<k → P.SingleSectorCone normal j) → (k=2 → P.DoubleSectorCone normal j) →
        k≤twoConeSlots axis normal := by
  obtain ⟨axis,hnorm,hsep,hcover⟩ := pentagon_angular_cone_cover D.rho D.a D.b D.g
    D.a_pos D.a_lt_two D.b_pos D.b_lt_two D.g_pos D.g_lt_two D.pair_left D.pair_right D.triple
  refine ⟨axis,hnorm,hsep,?_⟩
  intro normal hnormal k hk hs hd
  obtain ⟨θ,hθ,hphase⟩ := exists_relative_unitAngleVector normal hnormal D.rho 0
  rw [zero_add] at hθ
  rw [← hphase] at hs hd ⊢
  exact hcover θ k hk (fun h => D.single_angles θ hθ (hs h)) (fun h => D.double_angles θ hθ (hd h))

end PentagonFaceBoundary.SectorAngleData

theorem PentagonFaceBoundary.sector_covering_axes {n : ℕ} {G : PennyGraph n} {F : PlaneFace G}
    (P : PentagonFaceBoundary G F) (ht : G.TriangleFree) (hF : F∈G.defectPlaneFaces ht)
    (hdegree : ∀ v a, G.graph.Adj v a → ∃ b, G.graph.Adj v b ∧ b≠a) (j : Fin 5) :
    ∃ axis : Bool→Plane,(∀ c,‖axis c‖=1) ∧ |inner ℝ (axis false) (axis true)|≤1/2 ∧
      ∀ (normal : Plane),‖normal‖=1 → ∀ k : ℕ,k≤2 →
        (0<k → P.SingleSectorCone normal j) → (k=2 → P.DoubleSectorCone normal j) →
        k≤twoConeSlots axis normal := by
  obtain ⟨D⟩ := P.exists_sector_angle_data ht hF hdegree j
  exact D.exists_covering_axes

end Swanepoel
