module
public import Swanepoel.LatticeEdges
public import Swanepoel.SharpnessArithmetic
@[expose] public section

noncomputable section
namespace Swanepoel

theorem sharpness : Sharpness := by
  intro n hn
  obtain ⟨w,h,r,hw,hh,hr,hsize,hedges⟩ := sharp_grid_parameters n hn
  have hcard : (gridShape w h r).card = n := by rw [gridShape_card]; exact hsize
  refine ⟨latticeConfiguration (gridShape w h r) hcard,
    latticeConfiguration_triangleFree _ hcard, ?_⟩
  rw [gridShape_edgeCount _ _ _ hh hr]
  exact hedges

end Swanepoel
