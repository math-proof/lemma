/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneBlocksGenerated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneRawGenerated
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk000.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk001.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk002.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk003.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk004.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk005.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk006.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk007.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk008.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk009.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk010.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk011.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk012.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk013.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk014.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk015.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk016.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk017.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk018.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk019.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk020.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk021.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk022.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk023.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk024.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk025.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk026.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk027.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk028.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk029.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk030.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk031.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk032.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk033.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk034.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk035.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk036.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk037.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk038.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk039.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk040.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk041.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk042.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk043.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk044.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk045.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk046.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk047.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk048.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk049.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk050.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk051.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk052.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk053.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk054.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk055.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk056.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk057.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk058.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk059.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk060.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk061.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk062.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk063.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk064.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk065.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk066.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk067.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk068.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk069.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk070.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk071.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk072.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk073.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk074.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk075.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk076.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk077.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk078.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk079.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk080.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk081.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk082.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk083.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk084.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk085.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk086.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk087.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk088.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk089.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk090.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk091.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk092.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk093.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk094.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk095.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk096.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk097.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk098.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk099.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk100.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk101.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk102.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk103.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk104.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk105.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk106.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk107.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk108.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk109.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk110.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk111.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk112.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk113.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk114.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk115.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk116.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk117.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk118.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk119.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk120.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk121.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk122.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk123.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk124.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk125.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk126.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk127.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk128.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk129.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk130.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk131.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk132.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk133.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk134.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk135.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk136.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk137.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk138.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk139.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk140.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk141.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk142.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk143.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk144.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk145.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk146.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk147.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk148.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk149.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk150.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk151.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk152.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk153.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk154.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk155.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk156.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk157.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk158.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk159.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk160.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk161.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk162.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk163.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk164.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk165.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk166.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk167.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk168.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk169.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk170.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk171.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk172.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk173.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk174.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk175.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk176.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk177.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk178.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk179.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk180.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk181.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk182.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk183.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk184.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk185.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk186.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk187.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk188.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk189.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk190.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk191.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk192.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk193.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk194.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk195.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk196.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk197.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk198.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk199.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk200.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk201.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk202.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk203.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk204.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk205.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk206.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk207.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk208.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk209.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk210.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk211.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk212.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk213.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk214.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk215.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk216.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk217.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk218.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk219.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk220.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk221.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk222.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk223.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk224.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk225.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk226.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk227.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk228.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk229.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk230.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk231.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk232.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk233.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk234.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk235.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk236.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk237.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk238.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk239.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk240.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk241.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk242.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk243.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk244.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk245.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk246.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk247.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk248.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk249.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk250.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk251.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk252.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk253.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk254.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.NOneCertificateChunks.Chunk255.Part3


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

def generatedCoefficientBlock0 : List Int :=
  [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 6, 0, 0, 0, 1, 0, 0,
    0, 0, 4, 0, 17, 0, 6, 0, 4, 0,
    0, 0, 0, 30, 0, 43, 0, 28, 0, 4,
    0, 0, 20, 0, 113, 0, 118, 0, 45, 0,
    0, 2, 0, 161, 0, 331, 0, 280, 0, 22,
    0, 0, 102, 0, 662, 0, 986, 0, 321, 0,
    0, 11, 0, 788, 0, 2452, 0, 1761, 0, 138,
    0, 0, 294, 0, 3932, 0, 5970, 0, 1667, 0,
    0, 48, 0, 2931, 0, 12144, 0, 8857, 0, 637,
    1, 0, 1207, 0, 14334, 0, 24576, 0, 6101, 0,
    0, 228, 0, 10257, 0, 41758, 0, 25396, 0, 1261,
    6, 0, 3974, 0, 43968, 0, 64433, 0, 11957, 0,
    0, 652, 0, 28386, 0, 100975, 0, 50797, 0, 1632,
    24, 0, 10620, 0, 100176, 0, 121005, 0, 16766, 0,
    0, 1937, 0, 62413, 0, 181883, 0, 72494, 0, 2072,
    117, 0, 23524, 0, 176237, 0, 174097, 0, 20394, 0,
    0, 4606, 0, 109102, 0, 256723, 0, 86443, 0, 2249,
    292, 0, 41757, 0, 247717, 0, 204734, 0, 21527, 0,
    0, 9034, 0, 156796, 0, 301788, 0, 87533, 0, 2244,
    711, 0, 61630, 0, 290673, 0, 204602, 0, 20098, 0,
    0, 14027, 0, 187058, 0, 304834, 0, 78470, 0, 1957,
    1341, 0, 77153, 0, 297621, 0, 179739, 0, 16349, 0,
    0, 17970, 0, 193058, 0, 267504, 0, 62308, 0, 1500,
    2034, 0, 82881, 0, 269810, 0, 140825, 0, 12175, 0,
    0, 20569, 0, 179756, 0, 210430, 0, 44606, 0, 1051,
    2333, 0, 77812, 0, 215758, 0, 100045, 0, 8291, 0,
    0, 20455, 0, 150483, 0, 151122, 0, 29945, 0, 701,
    2317, 0, 65831, 0, 156390, 0, 65566, 0, 5164, 0,
    0, 17813, 0, 112738, 0, 98132, 0, 18340, 0, 422,
    2139, 0, 53025, 0, 104705, 0, 40736, 0, 3146, 0,
    0, 14100, 0, 76203, 0, 60711, 0, 10733, 0, 247,
    1791, 0, 37338, 0, 64612, 0, 23210, 0, 1733, 0,
    0, 10150, 0, 48219, 0, 35162, 0, 5993, 0, 126,
    1261, 0, 23895, 0, 36682, 0, 12779, 0, 904, 0,
    0, 7377, 0, 28034, 0, 19224, 0, 3062, 0, 73,
    857, 0, 14148, 0, 20823, 0, 6788, 0, 464, 0,
    0, 4160, 0, 15083, 0, 9886, 0, 1534, 0, 26,
    554, 0, 7745, 0, 10519, 0, 3225, 0, 211, 0,
    0, 2370, 0, 7870, 0, 5080, 0, 733, 0, 15,
    339, 0, 3829, 0, 5174, 0, 1631, 0, 81, 0,
    0, 1140, 0, 3968, 0, 2332, 0, 305, 0, 5,
    165, 0, 1755, 0, 2541, 0, 679, 0, 41, 0,
    0, 508, 0, 1626, 0, 1065, 0, 129, 0, 1,
    72, 0, 817, 0, 1120, 0, 325, 0, 12, 0,
    0, 212, 0, 832, 0, 501, 0, 51, 0, 1,
    18, 0, 303, 0, 473, 0, 105, 0, 3, 0,
    0, 56, 0, 274, 0, 174, 0, 19, 0, 0,
    11, 0, 109, 0, 209, 0, 51, 0, 2, 0,
    0, 27, 0, 129, 0, 89, 0, 3, 0, 0,
    0, 0, 42, 0, 78, 0, 21, 0, 0, 0,
    0, 2, 0, 38, 0, 23, 0, 3, 0, 0,
    1, 0, 4, 0, 25, 0, 0, 0, 0, 0,
    0, 2, 0, 14, 0, 13, 0, 0, 0, 0,
    0, 0, 4, 0, 12, 0, 4, 0, 0, 0,
    0, 0, 0, 2, 0, 4, 0, 0, 0, 0,
    0, 0, 0, 0, 2, 0, 0, 0, 0, 0,
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  ]

end StatMech.FrontierA.NOneSymmetricMeanCertificate
