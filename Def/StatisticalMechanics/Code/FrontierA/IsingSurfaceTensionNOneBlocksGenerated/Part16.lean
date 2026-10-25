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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneBlocksGenerated.Part15


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

def generatedCoefficientBlock15 : List Int :=
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
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 4, 0, 0,
    0, 0, 4, 0, 0, 0, 22, 0, 0, 0,
    0, 8, 0, 34, 0, 46, 0, 23, 0, 0,
    4, 0, 83, 0, 154, 0, 140, 0, 0, 0,
    0, 82, 0, 407, 0, 495, 0, 110, 0, 0,
    29, 0, 646, 0, 1417, 0, 718, 0, 14, 0,
    0, 487, 0, 2772, 0, 2812, 0, 384, 0, 0,
    136, 0, 3002, 0, 7037, 0, 2791, 0, 83, 0,
    0, 1691, 0, 10524, 0, 10472, 0, 1343, 0, 0,
    396, 0, 9486, 0, 22634, 0, 8491, 0, 307, 0,
    0, 4296, 0, 29275, 0, 28431, 0, 3835, 0, 10,
    774, 0, 21167, 0, 53375, 0, 21001, 0, 839, 0,
    0, 8419, 0, 59995, 0, 59766, 0, 8875, 0, 50,
    1311, 0, 39304, 0, 100264, 0, 41598, 0, 1945, 0,
    0, 13483, 0, 99256, 0, 103931, 0, 17170, 0, 147,
    1868, 0, 57976, 0, 154819, 0, 68760, 0, 3756, 0,
    0, 18207, 0, 139334, 0, 154063, 0, 28422, 0, 352,
    2298, 0, 73927, 0, 206049, 0, 99112, 0, 6479, 0,
    0, 20775, 0, 167780, 0, 200231, 0, 40326, 0, 621,
    2326, 0, 81031, 0, 242284, 0, 126681, 0, 9442, 0,
    0, 20611, 0, 180591, 0, 230574, 0, 51316, 0, 959,
    2179, 0, 78825, 0, 254915, 0, 147296, 0, 12384, 0,
    0, 18124, 0, 173728, 0, 242266, 0, 59535, 0, 1329,
    1707, 0, 68124, 0, 246457, 0, 153836, 0, 14228, 0,
    0, 14524, 0, 151763, 0, 232950, 0, 63816, 0, 1531,
    1300, 0, 54683, 0, 218113, 0, 150048, 0, 15364, 0,
    0, 10289, 0, 121289, 0, 209904, 0, 62573, 0, 1742,
    861, 0, 39016, 0, 177083, 0, 135350, 0, 15366, 0,
    0, 7120, 0, 90156, 0, 175435, 0, 57743, 0, 1639,
    534, 0, 26420, 0, 135452, 0, 115744, 0, 14376, 0,
    0, 4284, 0, 60837, 0, 136618, 0, 49748, 0, 1628,
    340, 0, 16670, 0, 95620, 0, 93881, 0, 12751, 0,
    0, 2464, 0, 39370, 0, 101062, 0, 40647, 0, 1422,
    147, 0, 9439, 0, 62431, 0, 70519, 0, 10641, 0,
    0, 1382, 0, 23700, 0, 69944, 0, 32456, 0, 1196,
    101, 0, 5212, 0, 39478, 0, 51410, 0, 8289, 0,
    0, 658, 0, 12600, 0, 44554, 0, 23873, 0, 1062,
    47, 0, 2659, 0, 22937, 0, 35876, 0, 6603, 0,
    0, 334, 0, 7042, 0, 27991, 0, 17033, 0, 727,
    8, 0, 1310, 0, 12114, 0, 21791, 0, 4834, 0,
    0, 122, 0, 3383, 0, 16281, 0, 12209, 0, 588,
    15, 0, 455, 0, 6423, 0, 14215, 0, 3273, 0,
    0, 70, 0, 1386, 0, 8367, 0, 7549, 0, 486,
    2, 0, 283, 0, 3262, 0, 8641, 0, 2591, 0,
    0, 18, 0, 695, 0, 4381, 0, 4519, 0, 252,
    0, 0, 74, 0, 1182, 0, 3918, 0, 1458, 0,
    0, 4, 0, 237, 0, 2427, 0, 3212, 0, 249,
    1, 0, 14, 0, 585, 0, 2313, 0, 1044, 0,
    0, 4, 0, 74, 0, 799, 0, 1597, 0, 159,
    0, 0, 14, 0, 230, 0, 1397, 0, 611, 0,
    0, 0, 0, 24, 0, 341, 0, 545, 0, 68,
    0, 0, 0, 0, 52, 0, 385, 0, 384, 0,
    0, 0, 0, 4, 0, 203, 0, 667, 0, 89,
    0, 0, 0, 0, 17, 0, 170, 0, 216, 0,
    0, 0, 0, 0, 0, 35, 0, 198, 0, 27,
    0, 0, 0, 0, 0, 0, 124, 0, 38, 0,
    0, 0, 0, 0, 0, 5, 0, 10, 0, 24,
    0, 0, 0, 0, 0, 0, 28, 0, 121, 0,
    0, 0, 0, 0, 0, 0, 0, 69, 0, 17,
    0, 0, 0, 0, 0, 0, 0, 0, 5, 0,
    0, 0, 0, 0, 0, 0, 0, 17, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 9,
    0, 0, 0, 0, 0, 0, 0, 0, 14, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1
  ]

end StatMech.FrontierA.NOneSymmetricMeanCertificate
