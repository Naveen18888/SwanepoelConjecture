module
public import Swanepoel.SpineBankWinding
@[expose] public section

noncomputable section
namespace Swanepoel
open Set

theorem PositiveCellStep.winding_probe_coordU {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {e f : OrientedEdge G} (C : RhombusCell G)
    (hE : e.val=(C.a,C.b)) (hF : f.val=(C.d,C.c)) (r : ℝ) :
    C.coordU (windingNormalProbe (edgeCenter e) (edgeCenter f) r)=
      1/2+r/cross2 C.u C.v := by
  have heq : e=C.edgeAB := Subtype.ext hE
  have hfq : f=C.edgeDC := Subtype.ext hF
  have hm : stepCenter e f=C.center := by rw [heq,hfq,C.stepCenter_eq]
  have hv : edgeCenter e-edgeCenter f= -C.v := by
    have hh : edgeCenter f-edgeCenter e=C.v := by
      simpa only [edgeCenter,hE,hF] using C.spine_step
    rw [← hh]
    abel
  have hp : windingNormalProbe (edgeCenter e) (edgeCenter f) r=
      C.center+r • quarterTurn (-C.v) := by
    change stepCenter e f+r • quarterTurn (edgeCenter e-edgeCenter f)=_
    rw [hm,hv]
  have hnorm : ‖C.v‖=1 := by simpa only [RhombusCell.v,← dist_eq_norm] using C.da.2
  have hq : cross2 (quarterTurn (-C.v)) C.v=1 := by
    rw [quarterTurn_neg,cross2_neg_left]
    have hh : cross2 (quarterTurn C.v) C.v= -cross2 C.v (quarterTurn C.v) := by
      unfold cross2
      ring
    rw [hh,cross_quarterTurn,hnorm]
    norm_num
  have hvec : windingNormalProbe (edgeCenter e) (edgeCenter f) r-G.point C.a=
      (1/2:ℝ) • C.u+(1/2:ℝ) • C.v+r • quarterTurn (-C.v) := by
    rw [hp,← C.cellPoint_half_eq_center]
    dsimp [RhombusCell.cellPoint]
    module
  unfold RhombusCell.coordU
  rw [hvec,cross2_add_left,cross2_add_left,cross2_smul_left,cross2_smul_left,
    cross2_smul_left,cross2_self,hq]
  field_simp [C.cross_ne_zero ht]
  ring

theorem PositiveSpineChain.open_cell_positive_bank {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t e f : OrientedEdge G} (p : PositiveSpineChain G s t)
    (htop : ¬∃g,PositiveCellStep t g) (he : OnSpine s t e)
    (C : RhombusCell G) (hE : e.val=(C.a,C.b)) (hF : f.val=(C.d,C.c))
    (hpos : 0<cross2 C.u C.v) {z : Plane} (hz : z∈C.openRegion)
    (hside : 1/2<C.coordU z) : z∈p.bankRegion 1 := by
  have hd : C.coordU z-1/2∈Ioc (0:ℝ) (1/2) := ⟨by linarith,by linarith [hz.2.1]⟩
  have hq : C.coordV z∈Icc (0:ℝ) 1 := ⟨hz.2.2.1.le,hz.2.2.2.le⟩
  have hm := p.cellPoint_mem_bank ht htop he C hE hF hpos 1 (C.coordU z-1/2) (C.coordV z) hd hq
  rw [show (1/2:ℝ)+1*(C.coordU z-1/2)=C.coordU z by ring,C.reconstruct ht z] at hm
  exact hm

theorem PositiveSpineChain.open_cell_negative_bank {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t e f : OrientedEdge G} (p : PositiveSpineChain G s t)
    (htop : ¬∃g,PositiveCellStep t g) (he : OnSpine s t e)
    (C : RhombusCell G) (hE : e.val=(C.a,C.b)) (hF : f.val=(C.d,C.c))
    (hpos : 0<cross2 C.u C.v) {z : Plane} (hz : z∈C.openRegion)
    (hside : C.coordU z<1/2) : z∈p.bankRegion (-1) := by
  have hd : 1/2-C.coordU z∈Ioc (0:ℝ) (1/2) := ⟨by linarith,by linarith [hz.1]⟩
  have hq : C.coordV z∈Icc (0:ℝ) 1 := ⟨hz.2.2.1.le,hz.2.2.2.le⟩
  have hm := p.cellPoint_mem_bank ht htop he C hE hF hpos (-1) (1/2-C.coordU z) (C.coordV z) hd hq
  rw [show (1/2:ℝ)+(-1)*(1/2-C.coordU z)=C.coordU z by ring,C.reconstruct ht z] at hm
  exact hm

theorem PositiveSpineChain.bankLabel_difference {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t e f : OrientedEdge G} (p : PositiveSpineChain G s t)
    (hs : ¬∃g,PositiveCellStep g s) (htop : ¬∃g,PositiveCellStep t g)
    (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val)
    (loop : PlaneChain (edgeCenter s) (edgeCenter s))
    (hloop : loop.trace⊆trackSpineTrace (edgeComponent s)∪outer.val)
    (he : OnSpine s t e) (hef : PositiveCellStep e f)
    (ε : ℝ) (hε : 0<ε)
    (hjump : ∀ r : ℝ, 0<r → r<ε →
      loop.windingIndex (windingNormalProbe (edgeCenter e) (edgeCenter f) (-r))=
        loop.windingIndex (windingNormalProbe (edgeCenter e) (edgeCenter f) r)+1) :
    p.bankLabel loop (-1)=p.bankLabel loop 1+1 := by
  obtain ⟨C,hE,hF,hpos⟩ := hef
  have heq : e=C.edgeAB := Subtype.ext hE
  have hfq : f=C.edgeDC := Subtype.ext hF
  have hm : windingNormalProbe (edgeCenter e) (edgeCenter f) 0=C.center := by
    have hh : stepCenter e f=C.center := by rw [heq,hfq,C.stepCenter_eq]
    simpa only [windingNormalProbe,zero_smul,add_zero,stepCenter,RhombusCell.midpoint2] using hh
  have hopen : IsOpen {r : ℝ | windingNormalProbe (edgeCenter e) (edgeCenter f) r∈C.openRegion} :=
    C.isOpen_openRegion.preimage (continuous_windingNormalProbe _ _)
  have hzero : (0:ℝ)∈{r : ℝ | windingNormalProbe (edgeCenter e) (edgeCenter f) r∈C.openRegion} := by
    rw [Set.mem_ofPred_eq,hm,← C.cellPoint_half_eq_center]
    exact C.cellPoint_mem_openRegion ht (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  let r := min ε δ/2
  have hr : 0<r := by dsimp [r]; positivity
  have hrε : r<ε := by have := min_le_left ε δ; dsimp [r]; linarith
  have hrδ : r<δ := by have := min_le_right ε δ; dsimp [r]; linarith
  have hp : windingNormalProbe (edgeCenter e) (edgeCenter f) r∈C.openRegion :=
    hball (by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hr] using hrδ)
  have hn : windingNormalProbe (edgeCenter e) (edgeCenter f) (-r)∈C.openRegion :=
    hball (by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_neg,abs_of_pos hr] using hrδ)
  have hcoordP := PositiveCellStep.winding_probe_coordU ht C hE hF r
  have hcoordN := PositiveCellStep.winding_probe_coordU ht C hE hF (-r)
  have hP : windingNormalProbe (edgeCenter e) (edgeCenter f) r∈p.bankRegion 1 :=
    p.open_cell_positive_bank ht htop he C hE hF hpos hp (by rw [hcoordP]; linarith [div_pos hr hpos])
  have hN : windingNormalProbe (edgeCenter e) (edgeCenter f) (-r)∈p.bankRegion (-1) :=
    p.open_cell_negative_bank ht htop he C hE hF hpos hn (by rw [hcoordN]; have := div_neg_of_neg_of_pos (neg_neg_of_pos hr) hpos; linarith)
  have hj := hjump r hr hrε
  rw [p.bankLabel_constant ht hs htop outer houter loop hloop (-1) (Or.inr rfl) hN,
    p.bankLabel_constant ht hs htop outer houter loop hloop 1 (Or.inl rfl) hP] at hj
  exact hj

end Swanepoel
