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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneBlocksGenerated.Part3


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

def generatedCoefficientBlock3 : List Int :=
  [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 2, 0, 0, 0, 0, 0, 0,
    0, 0, 4, 0, 8, 0, 2, 0, 0, 0,
    0, 2, 0, 26, 0, 29, 0, 20, 0, 0,
    0, 0, 30, 0, 117, 0, 136, 0, 22, 0,
    0, 14, 0, 227, 0, 504, 0, 228, 0, 4,
    2, 0, 222, 0, 1189, 0, 1151, 0, 159, 0,
    0, 95, 0, 1557, 0, 3458, 0, 1314, 0, 60,
    10, 0, 1184, 0, 6172, 0, 5626, 0, 880, 0,
    0, 451, 0, 6962, 0, 13723, 0, 5239, 0, 240,
    53, 0, 4627, 0, 21338, 0, 17540, 0, 2527, 0,
    0, 1595, 0, 21216, 0, 38247, 0, 13343, 0, 521,
    215, 0, 12670, 0, 53776, 0, 41009, 0, 5546, 0,
    0, 4220, 0, 48227, 0, 80097, 0, 26149, 0, 908,
    578, 0, 26840, 0, 103190, 0, 74767, 0, 9173, 0,
    0, 8522, 0, 86405, 0, 136143, 0, 41963, 0, 1294,
    1230, 0, 45899, 0, 162966, 0, 112424, 0, 12803, 0,
    0, 13929, 0, 127824, 0, 192538, 0, 56946, 0, 1631,
    1983, 0, 64071, 0, 216502, 0, 145376, 0, 15745, 0,
    0, 18889, 0, 161766, 0, 236880, 0, 67258, 0, 1788,
    2515, 0, 76606, 0, 253381, 0, 164988, 0, 17160, 0,
    0, 21433, 0, 179004, 0, 256382, 0, 71244, 0, 1874,
    2659, 0, 80581, 0, 262565, 0, 168742, 0, 17197, 0,
    0, 21079, 0, 176735, 0, 252013, 0, 68086, 0, 1724,
    2341, 0, 75742, 0, 248456, 0, 156995, 0, 15725, 0,
    0, 18437, 0, 158233, 0, 225955, 0, 61284, 0, 1624,
    1865, 0, 64105, 0, 212192, 0, 134579, 0, 13428, 0,
    0, 14405, 0, 130772, 0, 188500, 0, 50618, 0, 1288,
    1252, 0, 49385, 0, 169677, 0, 108743, 0, 10920, 0,
    0, 10128, 0, 99405, 0, 145664, 0, 39652, 0, 1010,
    852, 0, 35527, 0, 126034, 0, 81986, 0, 8340, 0,
    0, 6433, 0, 69498, 0, 105885, 0, 29467, 0, 802,
    427, 0, 23036, 0, 88273, 0, 58865, 0, 6076, 0,
    0, 3955, 0, 46760, 0, 72836, 0, 20721, 0, 519,
    224, 0, 13925, 0, 57860, 0, 40152, 0, 4353, 0,
    0, 2064, 0, 28190, 0, 47504, 0, 14102, 0, 404,
    118, 0, 7979, 0, 36084, 0, 25764, 0, 2812, 0,
    0, 1038, 0, 16595, 0, 29715, 0, 9073, 0, 275,
    32, 0, 3993, 0, 21140, 0, 16144, 0, 1898, 0,
    0, 493, 0, 8911, 0, 17591, 0, 5659, 0, 151,
    20, 0, 2022, 0, 11816, 0, 9601, 0, 1164, 0,
    0, 167, 0, 4367, 0, 9977, 0, 3354, 0, 130,
    7, 0, 876, 0, 6284, 0, 5494, 0, 678, 0,
    0, 81, 0, 2160, 0, 5431, 0, 1879, 0, 58,
    0, 0, 321, 0, 2917, 0, 2973, 0, 415, 0,
    0, 19, 0, 906, 0, 2911, 0, 1163, 0, 35,
    1, 0, 133, 0, 1484, 0, 1658, 0, 208, 0,
    0, 6, 0, 333, 0, 1278, 0, 474, 0, 29,
    0, 0, 37, 0, 633, 0, 807, 0, 120, 0,
    0, 1, 0, 124, 0, 648, 0, 318, 0, 3,
    0, 0, 8, 0, 200, 0, 422, 0, 65, 0,
    0, 0, 0, 46, 0, 335, 0, 164, 0, 9,
    0, 0, 1, 0, 96, 0, 152, 0, 15, 0,
    0, 0, 0, 4, 0, 71, 0, 41, 0, 2,
    0, 0, 0, 0, 30, 0, 111, 0, 21, 0,
    0, 0, 0, 1, 0, 48, 0, 45, 0, 0,
    0, 0, 0, 0, 4, 0, 34, 0, 4, 0,
    0, 0, 0, 0, 0, 19, 0, 9, 0, 1,
    0, 0, 0, 0, 0, 0, 3, 0, 0, 0,
    0, 0, 0, 0, 0, 2, 0, 8, 0, 0,
    0, 0, 0, 0, 0, 0, 11, 0, 2, 0,
    0, 0, 0, 0, 0, 0, 0, 2, 0, 0,
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
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
