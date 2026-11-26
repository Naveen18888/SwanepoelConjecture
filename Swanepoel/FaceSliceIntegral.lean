module
public import Swanepoel.FaceSliceReconstruction
public import Swanepoel.FiniteSliceIntegral
@[expose] public section

noncomputable section
namespace Swanepoel
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem ContactEdge.sliceHeight_bounds {n : ℕ} {G : PennyGraph n} (e : ContactEdge G)
    {x R : ℝ} (he : e∈G.sliceEdges x)
    (hv : ∀ v : Fin n,|G.point v 1|<R) : -R<e.sliceHeight x ∧ e.sliceHeight x<R := by
  have ht := e.sliceParameter_bounds he
  have ha := abs_lt.mp (hv e.val.1)
  have hb := abs_lt.mp (hv e.val.2)
  have hlo := positive_weighted_average (sub_nonneg.mpr ht.2.2.le) ht.2.1.le
    (by ring : 1-e.sliceParameter x+e.sliceParameter x=1)
    (by linarith only [ha.1] : 0<G.point e.val.1 1+R)
    (by linarith only [hb.1] : 0<G.point e.val.2 1+R)
  have hhi := positive_weighted_average (sub_nonneg.mpr ht.2.2.le) ht.2.1.le
    (by ring : 1-e.sliceParameter x+e.sliceParameter x=1)
    (by linarith only [ha.2] : 0<R-G.point e.val.1 1)
    (by linarith only [hb.2] : 0<R-G.point e.val.2 1)
  dsimp [ContactEdge.sliceHeight]
  constructor <;> linarith only [hlo,hhi]

theorem PennyGraph.faceSlice_integral {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (hF : Bornology.IsBounded F.val) (R : ℝ)
    (hv : ∀ v : Fin n,|G.point v 1|<R)
    (hbound : ∀ z∈F.val,|z 1|<R)
    (x : ℝ) (hx : ∀ v : Fin n,x≠G.point v 0) :
    (∫ y,G.faceSliceValue F x y)=∑ e∈G.sliceEdges x,
      (faceIndicatorValue F e.sliceLowerFace-faceIndicatorValue F e.sliceUpperFace)*(e.sliceHeight x+R) := by
  rw [Finset.sum_subtype (G.sliceEdges x) (fun _ => Iff.rfl)]
  apply finite_slice_integral (fun e : SliceEdge G x => e.val.sliceHeight x)
    (fun e => faceIndicatorValue F e.val.sliceLowerFace-faceIndicatorValue F e.val.sliceUpperFace)
    (G.faceSliceValue F x) R
    (fun e => e.val.sliceHeight_bounds e.property hv) ?_
    (G.faceSliceValue_reconstruction F hF x hx)
  intro y hy
  apply ite_eq_right
  intro hz
  exact hy (abs_lt.mp (hbound (cartPoint x y) hz))

end Swanepoel
