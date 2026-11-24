CREATE TABLE `inverted` (
  name varchar(256) COLLATE utf8mb4_bin NOT NULL,
  id int NOT NULL COMMENT 'Owning axiom.lemma row ID',
  lemma_id int NOT NULL DEFAULT 0 COMMENT 'Zero-based declaration index in the Lean file',
  section enum('given', 'imply', 'proof') NOT NULL DEFAULT 'imply',
  latex_id int NOT NULL DEFAULT 0 COMMENT 'Zero-based latex formula index within the section',
  count int NOT NULL,
  PRIMARY KEY (name, id, lemma_id, section, latex_id)
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
PARTITION BY KEY() PARTITIONS 8
