/**
 * Data for `axiomSummary.vue`, mirroring `php/summary.php` + `php/utility.php`
 * (`_t_type`, `_t_matrix`, `select_lemma_by_error`, `select_count`).
 */
import { getMysqlConfig, getMysqlPool } from './fetchLemmaMysql.mjs';

function dbUser(projectUser) {
  const s = String(projectUser || 'lean');
  return /^[a-zA-Z0-9_]+$/.test(s) ? s : 'lean';
}

function cteType(u) {
  return `_t_type as (
    select
        distinct type
    from
        lemma
        cross join json_table(
            error,
            '$[*]' columns(type text path '$.type')
        ) as jt
    where
        user = '${u}'
)`;
}

function cteMatrix(u) {
  return `_t_matrix as (
    select
        module,
        type
    from
        lemma
        cross join json_table(
            error,
            '$[*]' columns(type text path '$.type')
        ) as jt
    where
        user = '${u}'
)`;
}

function section(axiom) {
  const i = String(axiom).indexOf('.');
  return i === -1 ? axiom : axiom.slice(0, i);
}

/**
 * @param {string} projectUser
 * @returns {Promise<{ state_count_pairs: { type: string, count: number }[], repertoire: Record<string, Record<string, string[]>> }>}
 */
export async function buildSummaryPayload(projectUser) {
  const empty = {
    state_count_pairs: [{ type: 'total', count: 0 }],
    repertoire: /** @type {Record<string, Record<string, string[]>>} */ ({}),
  };

  if (!getMysqlConfig()) {
    return empty;
  }

  const u = dbUser(projectUser);
  const p = getMysqlPool();
  if (!p) {
    return empty;
  }

  try {
    const tt = cteType(u);
    const tm = cteMatrix(u);

    const sqlRepertoire = `
with ${tt}, ${tm}
select
    _t_matrix.module as module,
    json_unquote(json_extract(json_arrayagg(_t_type.type), '$[0]')) as err_type
from
    _t_matrix
    join _t_type using (type)
group by
    module`;

    const [repRows] = await p.query(sqlRepertoire);
    const repertoire = { ...empty.repertoire };
    if (Array.isArray(repRows)) {
      for (const row of repRows) {
        const axiom = row.module;
        const t = row.err_type;
        if (!axiom || typeof t !== 'string') continue;
        const sec = section(axiom);
        if (!repertoire[sec]) repertoire[sec] = {};
        if (!repertoire[sec][t]) repertoire[sec][t] = [];
        repertoire[sec][t].push(axiom);
      }
    }

    const sqlCounts = `
with ${tt}, ${tm}
select
    _t_type.type,
    count(distinct _t_matrix.module) as count
from
    _t_type
    join _t_matrix using (type)
group by
    type`;

    const [countRows] = await p.query(sqlCounts);
    const state_count_pairs = [];
    if (Array.isArray(countRows)) {
      for (const row of countRows) {
        state_count_pairs.push({
          type: String(row.type),
          count: Number(row.count) || 0,
        });
      }
    }

    const [totalRows] = await p.query(
      `select count(*) as c from lemma where user = ? and json_length(imports) > 0`,
      [u]
    );
    const total =
      Array.isArray(totalRows) && totalRows[0]
        ? Number(totalRows[0].c) || 0
        : 0;
    state_count_pairs.push({ type: 'total', count: total });

    return { state_count_pairs, repertoire };
  } catch (e) {
    console.warn('[summary mysql]', /** @type {Error} */ (e).message);
    return empty;
  }
}
