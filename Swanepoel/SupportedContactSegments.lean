module
public import Swanepoel.EdgeNeighbourhood
@[expose] public section

noncomputable section
namespace Swanepoel

theorem PennyGraph.supported_contact_line_parameter {n : ℕ} (G : PennyGraph n)
    (a b : Fin n) (hab : G.graph.Adj a b) (u v z : Plane)
    (hub : 0 < inner ℝ u (G.point b-G.point a))
    (hva : 0 < inner ℝ v (G.point a-G.point b))
    (huz : 0 < inner ℝ u (z-G.point a)) (hvz : 0 < inner ℝ v (z-G.point b))
    (hc : cross2 (G.point b-G.point a) (z-G.point a)=0) :
    ∃ t∈Set.Ioo (0:ℝ) 1,G.edgePoint a b t=z := by
  let e := G.point b-G.point a
  let t := inner ℝ e (z-G.point a)
  have he : ‖e‖=1 := by simpa only [e,← dist_eq_norm] using hab.symm.2
  have hce : cross2 e (z-G.point a)=0 := hc
  have hrepr : z-G.point a=t • e := by
    simpa only [t,hce,zero_smul,add_zero] using unit_direction_decomposition e (z-G.point a) he
  have hreprB : z-G.point b=(t-1) • e := by
    calc
      _ = (z-G.point a)-e := by dsimp [e]; abel
      _ = _ := by rw [hrepr]; module
  have ht0 : 0<t := by
    rw [hrepr,real_inner_smul_right] at huz
    exact (mul_pos_iff.mp huz).resolve_right (fun h => hub.not_gt h.2) |>.1
  have hve : inner ℝ v e<0 := by
    have hn : G.point a-G.point b= -e := by dsimp [e]; abel
    rw [hn,inner_neg_right] at hva
    linarith
  have ht1 : t<1 := by
    rw [hreprB,real_inner_smul_right] at hvz
    have hneg := (mul_pos_iff.mp hvz).resolve_left (fun h => hve.not_gt h.2)
    linarith [hneg.1]
  refine ⟨t,⟨ht0,ht1⟩,?_⟩
  dsimp [PennyGraph.edgePoint]
  have hz : z=G.point a+t • e := by rw [← hrepr]; abel
  rw [hz]
  dsimp [e]
  module

theorem PennyGraph.supported_contact_cross_ne_zero {n : ℕ} (G : PennyGraph n)
    (a b c : Fin n) (hab : G.graph.Adj a b) (hca : c≠a) (u v : Plane)
    (hub : 0 < inner ℝ u (G.point b-G.point a))
    (hva : 0 < inner ℝ v (G.point a-G.point b))
    (huc : 0 < inner ℝ u (G.point c-G.point a))
    (hvc : 0 < inner ℝ v (G.point c-G.point b)) :
    cross2 (G.point b-G.point a) (G.point c-G.point a)≠0 := by
  intro hc
  obtain ⟨t,ht,hpoint⟩ := G.supported_contact_line_parameter a b hab u v (G.point c) hub hva huc hvc hc
  have hd := G.edgePoint_dist_start a b hab ht.1.le
  rw [hpoint] at hd
  have hs := G.separated c a hca
  linarith [ht.2]

theorem PennyGraph.supported_nonincident_edge_cross_nonneg {n : ℕ} (G : PennyGraph n)
    (a b c d : Fin n) (hab : G.graph.Adj a b) (hcd : G.graph.Adj c d)
    (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (u v : Plane)
    (hub : 0 < inner ℝ u (G.point b-G.point a))
    (hva : 0 < inner ℝ v (G.point a-G.point b))
    (huc : 0 < inner ℝ u (G.point c-G.point a))
    (hud : 0 < inner ℝ u (G.point d-G.point a))
    (hvc : 0 < inner ℝ v (G.point c-G.point b))
    (hvd : 0 < inner ℝ v (G.point d-G.point b)) :
    0≤cross2 (G.point b-G.point a) (G.point c-G.point a)*
      cross2 (G.point b-G.point a) (G.point d-G.point a) := by
  by_contra hn
  have hneg := lt_of_not_ge hn
  let e := G.point b-G.point a
  let C := cross2 e (G.point c-G.point a)
  let D := cross2 e (G.point d-G.point a)
  change C*D<0 at hneg
  have hden : C-D≠0 := by
    intro h
    have heq : C=D := sub_eq_zero.mp h
    rw [heq] at hneg
    nlinarith [sq_nonneg D]
  let s := C/(C-D)
  have hs0 : 0<s := by
    rcases mul_neg_iff.mp hneg with h | h
    · exact div_pos h.1 (by linarith [h.2])
    · exact div_pos_of_neg_of_neg h.1 (by linarith [h.2])
  have hs1 : s<1 := by
    rcases mul_neg_iff.mp hneg with h | h
    · exact (div_lt_one (by linarith [h.1,h.2] : 0<C-D)).mpr (by linarith [h.2])
    · exact (div_lt_one_of_neg (by linarith [h.1,h.2] : C-D<0)).mpr (by linarith [h.2])
  have hs : s*(C-D)=C := div_mul_cancel₀ _ hden
  let z := G.edgePoint c d s
  have hz (w : Plane) : z-w=(1-s) • (G.point c-w)+s • (G.point d-w) := by
    dsimp [z,PennyGraph.edgePoint]
    module
  have huz : 0 < inner ℝ u (z-G.point a) := by
    rw [hz,inner_add_right,real_inner_smul_right,real_inner_smul_right]
    exact add_pos (mul_pos (by linarith) huc) (mul_pos hs0 hud)
  have hvz : 0 < inner ℝ v (z-G.point b) := by
    rw [hz,inner_add_right,real_inner_smul_right,real_inner_smul_right]
    exact add_pos (mul_pos (by linarith) hvc) (mul_pos hs0 hvd)
  have hc : cross2 e (z-G.point a)=0 := by
    rw [hz,cross2_add_right,cross2_smul_right,cross2_smul_right]
    change (1-s)*C+s*D=0
    nlinarith [hs]
  obtain ⟨t,ht,hpoint⟩ := G.supported_contact_line_parameter a b hab u v z hub hva huz hvz hc
  exact G.disjoint_unit_edges a b c d hab hcd hac had hbc hbd t s
    ht.1.le ht.2.le hs0.le hs1.le hpoint

end Swanepoel
