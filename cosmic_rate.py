import numpy as np

# Area
scint_size = 0.72  # Side length (m)
scint_area = scint_size ** 2

# Distance between scintillators
distance = .40  # m

# Number of samples
N = 10**6

# Direction sampling
cos_theta = np.random.uniform(0, 1, N)
theta = np.arccos(cos_theta)
phi = np.random.uniform(0, 2*np.pi, N)

# Weight cos^2θ
intensity_weight = cos_theta ** 2

# Assuming start from the center of top surface, randomly sample x, y coordinates passing through first scintillator
x0 = np.random.uniform(-scint_size/2, scint_size/2, N)
y0 = np.random.uniform(-scint_size/2, scint_size/2, N)

# Calculate coordinates when reaching the lower scintillator
dx = np.tan(theta) * np.cos(phi) * distance
dy = np.tan(theta) * np.sin(phi) * distance

x1 = x0 + dx
y1 = y0 + dy

# Check if particle hits the lower scintillator
hits = (
    (np.abs(x1) <= scint_size/2) &
    (np.abs(y1) <= scint_size/2)
)

# Calculate effective solid angle using cos^2 weighting (using 2π × average cos^2)
effective_solid_angle = np.sum(intensity_weight[hits]) / N * 2 * np.pi

# Cosmic muon rate based on vertical flux (above 2 GeV, rough estimate)
# Cosmic muon rate based on vertical flux (PDG, above 1 GeV)
flux_above_2GeV = 31.48  # muons/m²/s/sr
flux_above_1GeV = 70  # muons/m²/s/sr

rate_above_2GeV = flux_above_2GeV * scint_area * effective_solid_angle
rate_above_1GeV = flux_above_1GeV * scint_area * effective_solid_angle

print(effective_solid_angle, rate_above_1GeV, rate_above_2GeV)
