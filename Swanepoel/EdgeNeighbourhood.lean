module
public import Swanepoel.ContactSubdrawing
@[expose] public section

noncomputable section
namespace Swanepoel

def quarterTurn (u : Plane) : Plane :=
  EuclideanSpace.single 0 (-u 1)+EuclideanSpace.single 1 (u 0)

theorem cross_quarterTurn (u : Plane) : cross2 u (quarterTurn u)=‖u‖^2 := by
  simp [quarterTurn,cross2,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]
  ring

theorem cross_quarterTurn_right (u w : Plane) : cross2 w (quarterTurn u)=inner ℝ u w := by
  simp [quarterTurn,cross2,PiLp.inner_apply,Fin.sum_univ_two]

theorem quarterTurn_norm (u : Plane) : ‖quarterTurn u‖=‖u‖ := by
  have h : ‖quarterTurn u‖^2=‖u‖^2 := by
    simp [quarterTurn,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two,add_comm]
  nlinarith [norm_nonneg u,norm_nonneg (quarterTurn u)]

theorem unit_direction_decomposition (u w : Plane) (hu : ‖u‖=1) :
    w=inner ℝ u w • u+cross2 u w • quarterTurn u := by
  have hc : cross2 u (quarterTurn u)=1 := by rw [cross_quarterTurn,hu]; norm_num
  have h := cramer_reconstruct u (quarterTurn u) w (by rw [hc]; norm_num)
  rw [hc,cross_quarterTurn_right,div_one,div_one] at h
  exact h.symm

theorem PennyGraph.edgePoint_shift {n : ℕ} (G : PennyGraph n) (a b : Fin n) (t s : ℝ) :
    G.edgePoint a b (t+s)=G.edgePoint a b t+s • (G.point b-G.point a) := by
  dsimp [PennyGraph.edgePoint]
  module

theorem PennyGraph.cross_edgePoint_difference {n : ℕ} (G : PennyGraph n) (e : ContactEdge G)
    (t s : ℝ) :
    cross2 (G.point e.val.2-G.point e.val.1)
      (G.edgePoint e.val.1 e.val.2 s-G.edgePoint e.val.1 e.val.2 t)=0 := by
  have hd : G.edgePoint e.val.1 e.val.2 s-G.edgePoint e.val.1 e.val.2 t=
      (s-t) • (G.point e.val.2-G.point e.val.1) := by
    dsimp [PennyGraph.edgePoint]
    module
  rw [hd,cross2_smul_right,cross2_self,mul_zero]

theorem PennyGraph.edgeTrace_iff_cross_zero_in_ball {n : ℕ} (G : PennyGraph n)
    (e : ContactEdge G) {t r : ℝ} (hrt : r<t) (hr1 : r<1-t)
    {z : Plane} (hz : z∈Metric.ball (G.edgePoint e.val.1 e.val.2 t) r) :
    z∈G.edgeTrace e.val.1 e.val.2 ↔
      cross2 (G.point e.val.2-G.point e.val.1) (z-G.edgePoint e.val.1 e.val.2 t)=0 := by
  constructor
  · rintro ⟨s,_,rfl⟩
    exact G.cross_edgePoint_difference e t s
  · intro hc
    let u := G.point e.val.2-G.point e.val.1
    let p := G.edgePoint e.val.1 e.val.2 t
    let offset := inner ℝ u (z-p)
    have hu : ‖u‖=1 := by simpa only [u,← dist_eq_norm] using e.property.2.symm.2
    have he : z-p=offset • u := by
      have hd := unit_direction_decomposition u (z-p) hu
      rw [hc,zero_smul,add_zero] at hd
      exact hd
    have hoffset : |offset|<r := by
      rw [Metric.mem_ball,dist_eq_norm,he,norm_smul,hu,Real.norm_eq_abs,mul_one] at hz
      exact hz
    have h0 : 0≤t+offset := by have hh := (abs_lt.mp hoffset).1; linarith
    have h1 : t+offset≤1 := by have hh := (abs_lt.mp hoffset).2; linarith
    refine ⟨t+offset,⟨h0,h1⟩,?_⟩
    rw [G.edgePoint_shift]
    change p+offset • u=z
    rw [← he]
    abel

def leftHalfBall (u p : Plane) (r : ℝ) : Set Plane :=
  Metric.ball p r ∩ {z | cross2 u p<cross2 u z}

def rightHalfBall (u p : Plane) (r : ℝ) : Set Plane :=
  Metric.ball p r ∩ {z | cross2 u z<cross2 u p}

theorem isPreconnected_leftHalfBall (u p : Plane) (r : ℝ) : IsPreconnected (leftHalfBall u p r) :=
  ((convex_ball p r).inter ((convex_Ioi (cross2 u p)).linear_preimage (crossLinear u))).isPreconnected

theorem isPreconnected_rightHalfBall (u p : Plane) (r : ℝ) : IsPreconnected (rightHalfBall u p r) :=
  ((convex_ball p r).inter ((convex_Iio (cross2 u p)).linear_preimage (crossLinear u))).isPreconnected

theorem halfBalls_disjoint (u p : Plane) (r : ℝ) :
    _root_.Disjoint (leftHalfBall u p r) (rightHalfBall u p r) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨_,hl⟩ ⟨_,hr⟩
  change cross2 u p<cross2 u z at hl
  change cross2 u z<cross2 u p at hr
  exact (not_lt_of_ge hl.le) hr

theorem halfBalls_nonempty (u p : Plane) (hu : ‖u‖=1) {r : ℝ} (hr : 0<r) :
    (leftHalfBall u p r).Nonempty ∧ (rightHalfBall u p r).Nonempty := by
  have hnorm : ‖quarterTurn u‖=1 := by rw [quarterTurn_norm,hu]
  have hcross : cross2 u (quarterTurn u)=1 := by rw [cross_quarterTurn,hu]; norm_num
  have hball (a : ℝ) (ha : |a|<r) : p+a • quarterTurn u∈Metric.ball p r := by
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,hnorm,Real.norm_eq_abs,mul_one]
    exact ha
  constructor
  · refine ⟨p+(r/2) • quarterTurn u,hball _ (by rw [abs_of_pos (by linarith)]; linarith),?_⟩
    change cross2 u p<cross2 u (p+(r/2) • quarterTurn u)
    rw [cross2_add_right,cross2_smul_right,hcross]
    linarith
  · refine ⟨p+(-r/2) • quarterTurn u,hball _ (by rw [abs_of_neg (by linarith)]; linarith),?_⟩
    change cross2 u (p+(-r/2) • quarterTurn u)<cross2 u p
    rw [cross2_add_right,cross2_smul_right,hcross]
    linarith

theorem PennyGraph.insert_edge_ball_complement {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) {t r : ℝ}
    (hrt : r<t) (hr1 : r<1-t)
    (hfree : Metric.ball (G.edgePoint e.val.1 e.val.2 t) r⊆(G.subdrawing S)ᶜ) :
    Metric.ball (G.edgePoint e.val.1 e.val.2 t) r ∩ (G.subdrawing (insert e S))ᶜ=
        leftHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t) r ∪
        rightHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t) r := by
  classical
  rw [G.subdrawing_insert]
  ext z
  constructor
  · rintro ⟨hz,hnot⟩
    have hcross : cross2 (G.point e.val.2-G.point e.val.1)
        (z-G.edgePoint e.val.1 e.val.2 t)≠0 := by
      intro hc
      exact hnot (Or.inr ((G.edgeTrace_iff_cross_zero_in_ball e hrt hr1 hz).mpr hc))
    rw [cross2_sub_right,sub_ne_zero] at hcross
    rcases lt_or_gt_of_ne hcross with h | h
    · exact Or.inr ⟨hz,h⟩
    · exact Or.inl ⟨hz,h⟩
  · rintro (⟨hz,hs⟩ | ⟨hz,hs⟩)
    all_goals
      simp only [Set.mem_ofPred_eq] at hs
      refine ⟨hz,?_⟩
      rintro (hold | hnew)
      · exact hfree hz hold
      · have hc := (G.edgeTrace_iff_cross_zero_in_ball e hrt hr1 hz).mp hnew
        rw [cross2_sub_right,sub_eq_zero] at hc
        rw [hc] at hs
        exact (lt_irrefl _) hs

theorem PennyGraph.insert_edge_local_complement {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S)
    {t : ℝ} (ht0 : 0<t) (ht1 : t<1) : ∃ r : ℝ, 0<r ∧
      Metric.ball (G.edgePoint e.val.1 e.val.2 t) r ∩ (G.subdrawing (insert e S))ᶜ=
        leftHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t) r ∪
        rightHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t) r := by
  obtain ⟨r,hr,hrt,hr1,hfree⟩ := G.omitted_edge_free_ball S e he ht0 ht1
  exact ⟨r,hr,G.insert_edge_ball_complement S e hrt hr1 hfree⟩

end Swanepoel
