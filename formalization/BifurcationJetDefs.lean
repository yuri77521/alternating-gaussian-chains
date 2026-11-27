import BifurcationImages

namespace GaussianChains.Bifurcation.Images

/-- Even t-derivatives on the centered face, with the ordered-pair normalization. -/
noncomputable def curvatureAt (o : Order) (h : ℝ) : ℝ :=
  (3*kernelD o (1/2)-4*kernelD o (1/2+h)+2*kernelD o (1/2+2*h))/3

noncomputable def mixedAt (h : ℝ) : ℝ :=
  (-4*kernelD .third (1/2+h)+4*kernelD .third (1/2+2*h))/3

noncomputable def inwardAt (h : ℝ) : ℝ :=
  (kernelD .first h - kernelD .first (2*h) + kernelD .first (1/2-h) -
    kernelD .first (1/2-2*h))/3

end GaussianChains.Bifurcation.Images
