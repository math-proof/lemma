/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoSectorZeroMasks : Fin 4 -> Nat × Nat := ![
  (0x00, 0x00), (0x0f, 0x00), (0xf0, 0x00), (0xff, 0x00)
]


def sixVertexFourByTwoSectorOneMasks : Fin 28 -> Nat × Nat := ![
  (0x00, 0x11), (0x00, 0x22), (0x00, 0x44), (0x00, 0x88),
  (0x0f, 0x11), (0x0f, 0x22), (0x0f, 0x44), (0x0f, 0x88),
  (0x1e, 0x21), (0x2d, 0x42), (0x3c, 0x41), (0x4b, 0x84),
  (0x69, 0x82), (0x78, 0x81), (0x87, 0x18), (0x96, 0x28),
  (0xb4, 0x48), (0xc3, 0x14), (0xd2, 0x24), (0xe1, 0x12),
  (0xf0, 0x11), (0xf0, 0x22), (0xf0, 0x44), (0xf0, 0x88),
  (0xff, 0x11), (0xff, 0x22), (0xff, 0x44), (0xff, 0x88)
]


def sixVertexFourByTwoSectorTwoMasks : Fin 50 -> Nat × Nat := ![
  (0x00, 0x33), (0x00, 0x55), (0x00, 0x66), (0x00, 0x99),
  (0x00, 0xaa), (0x00, 0xcc), (0x0f, 0x33), (0x0f, 0x55),
  (0x0f, 0x66), (0x0f, 0x99), (0x0f, 0xaa), (0x0f, 0xcc),
  (0x1e, 0x65), (0x1e, 0xa9), (0x2d, 0x53), (0x2d, 0xca),
  (0x3c, 0x63), (0x3c, 0xc9), (0x4b, 0x95), (0x4b, 0xa6),
  (0x5a, 0xa5), (0x69, 0x93), (0x69, 0xc6), (0x78, 0xa3),
  (0x78, 0xc5), (0x87, 0x3a), (0x87, 0x5c), (0x96, 0x39),
  (0x96, 0x6c), (0xa5, 0x5a), (0xb4, 0x59), (0xb4, 0x6a),
  (0xc3, 0x36), (0xc3, 0x9c), (0xd2, 0x35), (0xd2, 0xac),
  (0xe1, 0x56), (0xe1, 0x9a), (0xf0, 0x33), (0xf0, 0x55),
  (0xf0, 0x66), (0xf0, 0x99), (0xf0, 0xaa), (0xf0, 0xcc),
  (0xff, 0x33), (0xff, 0x55), (0xff, 0x66), (0xff, 0x99),
  (0xff, 0xaa), (0xff, 0xcc)
]

def sixVertexFourByTwoSectorZeroArrows (i : Fin 4) :
    SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks
    (sixVertexFourByTwoSectorZeroMasks i).1
    (sixVertexFourByTwoSectorZeroMasks i).2

def sixVertexFourByTwoSectorOneArrows (i : Fin 28) :
    SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks
    (sixVertexFourByTwoSectorOneMasks i).1
    (sixVertexFourByTwoSectorOneMasks i).2

def sixVertexFourByTwoSectorTwoArrows (i : Fin 50) :
    SixVertexArrows sixVertexFourByTwoTorus :=
  sixVertexFourByTwoArrowsOfMasks
    (sixVertexFourByTwoSectorTwoMasks i).1
    (sixVertexFourByTwoSectorTwoMasks i).2

def sixVertexFourByTwoSourceIndexArrows (i : Fin 4 × Fin 50) :
    SixVertexArrows sixVertexFourByTwoTorus ×
      SixVertexArrows sixVertexFourByTwoTorus :=
  (sixVertexFourByTwoSectorZeroArrows i.1,
    sixVertexFourByTwoSectorTwoArrows i.2)

def sixVertexFourByTwoTargetIndexArrows (i : Fin 28 × Fin 28) :
    SixVertexArrows sixVertexFourByTwoTorus ×
      SixVertexArrows sixVertexFourByTwoTorus :=
  (sixVertexFourByTwoSectorOneArrows i.1,
    sixVertexFourByTwoSectorOneArrows i.2)


def sixVertexFourByTwoMatchingTable : Fin 200 -> Fin 28 × Fin 28 := ![
  (0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 3), (0, 5), (0, 6),
  (1, 6), (0, 7), (1, 7), (2, 7), (2, 8), (3, 8), (0, 9), (3, 9),
  (1, 10), (3, 10), (0, 11), (1, 11), (8, 11), (0, 12), (2, 12), (1, 13),
  (2, 13), (1, 14), (2, 14), (0, 15), (2, 15), (9, 14), (0, 16), (1, 16),
  (1, 17), (3, 17), (0, 18), (3, 18), (2, 19), (3, 19), (0, 21), (0, 22),
  (1, 22), (0, 23), (1, 23), (2, 23), (0, 25), (0, 26), (1, 26), (0, 27),
  (1, 27), (2, 27), (4, 1), (4, 2), (5, 2), (4, 3), (5, 3), (6, 3),
  (4, 5), (4, 6), (5, 6), (4, 7), (5, 7), (6, 7), (6, 8), (7, 8),
  (4, 9), (7, 9), (5, 10), (7, 10), (4, 11), (5, 11), (11, 8), (4, 12),
  (6, 12), (5, 13), (6, 13), (5, 14), (6, 14), (4, 15), (6, 15), (14, 9),
  (4, 16), (5, 16), (5, 17), (7, 17), (4, 18), (7, 18), (6, 19), (7, 19),
  (4, 21), (4, 22), (5, 22), (4, 23), (5, 23), (6, 23), (4, 25), (4, 26),
  (5, 26), (4, 27), (5, 27), (6, 27), (20, 1), (20, 2), (21, 2), (20, 3),
  (21, 3), (22, 3), (20, 5), (20, 6), (21, 6), (20, 7), (21, 7), (22, 7),
  (22, 8), (23, 8), (20, 9), (23, 9), (21, 10), (23, 10), (20, 11), (21, 11),
  (13, 18), (20, 12), (22, 12), (21, 13), (22, 13), (21, 14), (22, 14), (20, 15),
  (22, 15), (16, 19), (20, 16), (21, 16), (21, 17), (23, 17), (20, 18), (23, 18),
  (22, 19), (23, 19), (20, 21), (20, 22), (21, 22), (20, 23), (21, 23), (22, 23),
  (20, 25), (20, 26), (21, 26), (20, 27), (21, 27), (22, 27), (24, 1), (24, 2),
  (25, 2), (24, 3), (25, 3), (26, 3), (24, 5), (24, 6), (25, 6), (24, 7),
  (25, 7), (26, 7), (26, 8), (27, 8), (24, 9), (27, 9), (25, 10), (27, 10),
  (24, 11), (25, 11), (18, 13), (24, 12), (26, 12), (25, 13), (26, 13), (25, 14),
  (26, 14), (24, 15), (26, 15), (19, 16), (24, 16), (25, 16), (25, 17), (27, 17),
  (24, 18), (27, 18), (26, 19), (27, 19), (24, 21), (24, 22), (25, 22), (24, 23),
  (25, 23), (26, 23), (24, 25), (24, 26), (25, 26), (24, 27), (25, 27), (26, 27)
]


def sixVertexFourByTwoMatchingIndex (i : Fin 4 × Fin 50) :
    Fin 28 × Fin 28 :=
  sixVertexFourByTwoMatchingTable
    (finProdFinEquiv (m := 4) (n := 50) i)

end
end StatMech.FrontierD
