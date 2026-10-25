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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneBlocksGenerated.Part14


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

def generatedCoefficientBlock14 : List Int :=
  [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 2, 0, 0, 0, 0, 0, 0, 0, 0,
    2, 0, 10, 0, 2, 0, 0, 0, 0, 0,
    0, 16, 0, 26, 0, 14, 0, 0, 0, 0,
    6, 0, 62, 0, 68, 0, 40, 0, 0, 0,
    0, 56, 0, 198, 0, 175, 0, 38, 0, 0,
    18, 0, 338, 0, 592, 0, 269, 0, 8, 0,
    0, 262, 0, 1412, 0, 1306, 0, 190, 0, 0,
    68, 0, 1721, 0, 3998, 0, 1586, 0, 50, 0,
    0, 944, 0, 6849, 0, 6800, 0, 1026, 0, 0,
    178, 0, 6058, 0, 16007, 0, 6721, 0, 286, 0,
    0, 2678, 0, 20961, 0, 22518, 0, 3677, 0, 8,
    493, 0, 15541, 0, 43141, 0, 19466, 0, 991, 0,
    0, 6101, 0, 47482, 0, 54804, 0, 9673, 0, 47,
    1028, 0, 30576, 0, 87732, 0, 42860, 0, 2417, 0,
    0, 10785, 0, 85607, 0, 102379, 0, 20252, 0, 226,
    1607, 0, 49546, 0, 145194, 0, 75381, 0, 5148, 0,
    0, 15874, 0, 126794, 0, 157836, 0, 34259, 0, 576,
    2140, 0, 67111, 0, 202735, 0, 111500, 0, 8791, 0,
    0, 19677, 0, 161322, 0, 209395, 0, 49139, 0, 1034,
    2410, 0, 78294, 0, 243627, 0, 142270, 0, 12856, 0,
    0, 21051, 0, 179442, 0, 243671, 0, 62083, 0, 1552,
    2307, 0, 80495, 0, 262984, 0, 160909, 0, 15966, 0,
    0, 19680, 0, 178169, 0, 254502, 0, 69503, 0, 1886,
    2029, 0, 74113, 0, 253245, 0, 165761, 0, 17825, 0,
    0, 16730, 0, 160728, 0, 242603, 0, 69671, 0, 2040,
    1509, 0, 60902, 0, 224590, 0, 155524, 0, 17699, 0,
    0, 12677, 0, 131935, 0, 211911, 0, 65725, 0, 1964,
    1119, 0, 46868, 0, 184453, 0, 135541, 0, 15967, 0,
    0, 8722, 0, 99727, 0, 172770, 0, 56004, 0, 1813,
    669, 0, 32201, 0, 139406, 0, 109918, 0, 13769, 0,
    0, 5685, 0, 70818, 0, 131300, 0, 45277, 0, 1422,
    412, 0, 20582, 0, 99090, 0, 83822, 0, 10838, 0,
    0, 3247, 0, 45376, 0, 94665, 0, 34642, 0, 1196,
    219, 0, 12533, 0, 66341, 0, 59842, 0, 8166, 0,
    0, 1766, 0, 28016, 0, 63494, 0, 24557, 0, 858,
    93, 0, 6740, 0, 40843, 0, 41036, 0, 6004, 0,
    0, 882, 0, 15938, 0, 40862, 0, 16859, 0, 594,
    54, 0, 3407, 0, 24355, 0, 26706, 0, 3987, 0,
    0, 379, 0, 8162, 0, 24502, 0, 11068, 0, 471,
    16, 0, 1672, 0, 13396, 0, 16368, 0, 2667, 0,
    0, 167, 0, 4251, 0, 14168, 0, 6835, 0, 256,
    4, 0, 670, 0, 6759, 0, 9519, 0, 1708, 0,
    0, 54, 0, 1862, 0, 7708, 0, 4270, 0, 183,
    3, 0, 263, 0, 3368, 0, 5583, 0, 979, 0,
    0, 16, 0, 741, 0, 3706, 0, 2308, 0, 130,
    0, 0, 95, 0, 1586, 0, 2984, 0, 642, 0,
    0, 5, 0, 319, 0, 1927, 0, 1323, 0, 45,
    0, 0, 22, 0, 522, 0, 1341, 0, 315, 0,
    0, 0, 0, 90, 0, 891, 0, 809, 0, 47,
    0, 0, 4, 0, 246, 0, 746, 0, 175, 0,
    0, 0, 0, 30, 0, 279, 0, 316, 0, 21,
    0, 0, 0, 0, 92, 0, 388, 0, 119, 0,
    0, 0, 0, 0, 0, 132, 0, 152, 0, 3,
    0, 0, 0, 0, 9, 0, 90, 0, 38, 0,
    0, 0, 0, 1, 0, 60, 0, 121, 0, 10,
    0, 0, 0, 0, 3, 0, 53, 0, 25, 0,
    0, 0, 0, 0, 0, 5, 0, 30, 0, 1,
    0, 0, 0, 0, 0, 0, 28, 0, 10, 0,
    0, 0, 0, 0, 0, 1, 0, 4, 0, 0,
    0, 0, 0, 0, 0, 0, 4, 0, 8, 0,
    0, 0, 0, 0, 0, 0, 0, 11, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 2, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  ]

end StatMech.FrontierA.NOneSymmetricMeanCertificate
