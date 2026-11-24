CREATE TABLE `fingerprint` (
  id int NOT NULL COMMENT 'Owning axiom.lemma row ID',
  lemma_id int NOT NULL DEFAULT 0 COMMENT 'Zero-based declaration index in the Lean file',
  section enum('given', 'imply', 'proof') NOT NULL,
  latex_id int NOT NULL DEFAULT 0 COMMENT 'Zero-based latex formula index within the section',
  fingerprint json NOT NULL COMMENT 'Binder-aware search-JSON tree',
  PRIMARY KEY (id, lemma_id, section, latex_id)
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
