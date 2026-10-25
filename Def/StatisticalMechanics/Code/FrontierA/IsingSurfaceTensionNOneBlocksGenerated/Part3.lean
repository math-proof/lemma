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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneBlocksGenerated.Part2


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

def generatedCoefficientBlock2 : List Int :=
  [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 6, 0, 0, 0, 1, 0, 0, 0,
    0, 4, 0, 15, 0, 5, 0, 5, 0, 0,
    0, 0, 25, 0, 33, 0, 25, 0, 8, 0,
    0, 12, 0, 85, 0, 78, 0, 50, 0, 4,
    1, 0, 99, 0, 209, 0, 173, 0, 47, 0,
    0, 62, 0, 381, 0, 469, 0, 255, 0, 18,
    4, 0, 443, 0, 1028, 0, 916, 0, 204, 0,
    0, 125, 0, 1691, 0, 2467, 0, 1233, 0, 66,
    10, 0, 1127, 0, 4894, 0, 4482, 0, 924, 0,
    0, 387, 0, 5452, 0, 10847, 0, 4900, 0, 295,
    50, 0, 3391, 0, 16911, 0, 15686, 0, 2678, 0,
    0, 990, 0, 15770, 0, 33603, 0, 13327, 0, 543,
    88, 0, 8344, 0, 45264, 0, 40863, 0, 5854, 0,
    0, 2251, 0, 37464, 0, 77132, 0, 27837, 0, 913,
    216, 0, 18404, 0, 93225, 0, 78018, 0, 9752, 0,
    0, 4864, 0, 71615, 0, 138234, 0, 46123, 0, 1399,
    510, 0, 33264, 0, 155181, 0, 122288, 0, 14276, 0,
    0, 8628, 0, 112323, 0, 201523, 0, 63452, 0, 1748,
    975, 0, 51103, 0, 216444, 0, 160206, 0, 17812, 0,
    0, 13292, 0, 149957, 0, 251691, 0, 75598, 0, 2060,
    1583, 0, 66486, 0, 258623, 0, 181440, 0, 19356, 0,
    0, 17317, 0, 175313, 0, 274943, 0, 79315, 0, 2086,
    2052, 0, 75949, 0, 271931, 0, 183241, 0, 18731, 0,
    0, 19678, 0, 179991, 0, 266835, 0, 73441, 0, 1921,
    2369, 0, 77192, 0, 258433, 0, 164965, 0, 16633, 0,
    0, 19737, 0, 167240, 0, 234282, 0, 62419, 0, 1579,
    2293, 0, 70967, 0, 221567, 0, 135605, 0, 13182, 0,
    0, 17815, 0, 141394, 0, 188660, 0, 48117, 0, 1264,
    2017, 0, 58618, 0, 175166, 0, 101859, 0, 9983, 0,
    0, 14539, 0, 109712, 0, 139382, 0, 34927, 0, 863,
    1547, 0, 45314, 0, 128875, 0, 71705, 0, 6841, 0,
    0, 10758, 0, 79204, 0, 96395, 0, 23568, 0, 645,
    1146, 0, 31617, 0, 87477, 0, 47262, 0, 4582, 0,
    0, 7327, 0, 53777, 0, 62213, 0, 15016, 0, 408,
    726, 0, 20613, 0, 55585, 0, 29553, 0, 2924, 0,
    0, 4603, 0, 33684, 0, 38337, 0, 9104, 0, 250,
    421, 0, 12743, 0, 33948, 0, 17389, 0, 1693, 0,
    0, 2563, 0, 19676, 0, 22014, 0, 5367, 0, 159,
    231, 0, 7265, 0, 19101, 0, 9915, 0, 964, 0,
    0, 1360, 0, 10972, 0, 12469, 0, 2812, 0, 82,
    96, 0, 3707, 0, 10370, 0, 5377, 0, 542, 0,
    0, 705, 0, 5765, 0, 6470, 0, 1544, 0, 45,
    32, 0, 1832, 0, 5393, 0, 2734, 0, 245, 0,
    0, 268, 0, 2662, 0, 3374, 0, 794, 0, 18,
    14, 0, 834, 0, 2630, 0, 1384, 0, 134, 0,
    0, 127, 0, 1286, 0, 1607, 0, 318, 0, 13,
    2, 0, 326, 0, 1210, 0, 646, 0, 54, 0,
    0, 26, 0, 523, 0, 787, 0, 199, 0, 3,
    1, 0, 103, 0, 542, 0, 309, 0, 23, 0,
    0, 16, 0, 211, 0, 327, 0, 53, 0, 1,
    0, 0, 45, 0, 216, 0, 116, 0, 11, 0,
    0, 0, 0, 64, 0, 144, 0, 34, 0, 1,
    0, 0, 4, 0, 88, 0, 68, 0, 1, 0,
    0, 1, 0, 24, 0, 68, 0, 13, 0, 0,
    0, 0, 3, 0, 30, 0, 14, 0, 2, 0,
    0, 0, 0, 4, 0, 13, 0, 0, 0, 0,
    0, 0, 0, 0, 7, 0, 12, 0, 0, 0,
    0, 0, 0, 1, 0, 13, 0, 3, 0, 0,
    0, 0, 0, 0, 3, 0, 3, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
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
