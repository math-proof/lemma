CREATE TABLE `mathlib` (
  `name` varchar(256) COLLATE utf8mb4_bin NOT NULL PRIMARY KEY,
  `type` text,
  `instImplicit` text,
  `strictImplicit` text,
  `implicit` text,
  `explicit` text,
  `given` json,
  `default` text,
  `imply` json NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4
PARTITION BY KEY() PARTITIONS 8