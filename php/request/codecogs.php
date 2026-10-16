<?php
/**
 * Local proxy for latex.codecogs.com PNGs.
 * Chrome hits localhost (no Clash TLS); this script fetches CodeCogs with proxy disabled.
 *
 * Usage: php/request/codecogs.php?latex=<urlencoded formula>
 */
header_remove('X-Powered-By');

$latex = $_GET['latex'] ?? null;
if ($latex === null || $latex === '') {
    $qs = $_SERVER['QUERY_STRING'] ?? '';
    if ($qs !== '' && !str_contains($qs, '='))
        $latex = rawurldecode($qs);
}
if ($latex === null || $latex === '') {
    http_response_code(400);
    header('Content-Type: text/plain; charset=utf-8');
    echo 'missing latex';
    exit;
}
if (strlen($latex) > 8000) {
    http_response_code(414);
    header('Content-Type: text/plain; charset=utf-8');
    echo 'latex too long';
    exit;
}

$upstream = 'https://latex.codecogs.com/png.latex?' . rawurlencode($latex);

$body = false;
$code = 0;
$ctype = 'image/png';
$err = '';

// Prefer curl.exe --noproxy: PHP curl often still hits Clash MITM (self-signed chain).
$curlBin = null;
foreach ([
    'C:\\Windows\\System32\\curl.exe',
    'C:\\Windows\\SysWOW64\\curl.exe',
    'curl.exe',
    'curl',
] as $cand) {
    if ($cand === 'curl' || $cand === 'curl.exe') {
        $curlBin = $cand;
        break;
    }
    if (is_file($cand)) {
        $curlBin = $cand;
        break;
    }
}

$tmp = tempnam(sys_get_temp_dir(), 'cg');
if ($tmp === false) {
    http_response_code(500);
    header('Content-Type: text/plain; charset=utf-8');
    echo 'tempnam failed';
    exit;
}

$cmd = escapeshellarg($curlBin)
    . ' -sS --noproxy "*" -L --connect-timeout 10 --max-time 30'
    . ' -A ' . escapeshellarg('lemma-codecogs-proxy/1.1')
    . ' -o ' . escapeshellarg($tmp)
    . ' -w %{http_code}'
    . ' ' . escapeshellarg($upstream);

$out = [];
$ret = 0;
exec($cmd . ' 2>&1', $out, $ret);
$joined = trim(implode("\n", $out));
if (preg_match('/(\d{3})\s*$/', $joined, $m))
    $code = (int) $m[1];
else
    $code = 0;

if (is_readable($tmp)) {
    $body = file_get_contents($tmp);
}
@unlink($tmp);

if ($body === false || $body === '' || $code !== 200) {
    // Fallback: PHP curl with proxy cleared + SSL verify off (Clash MITM / env proxy).
    if (function_exists('curl_init')) {
        foreach (['http_proxy', 'https_proxy', 'HTTP_PROXY', 'HTTPS_PROXY', 'ALL_PROXY', 'all_proxy'] as $k) {
            putenv("$k=");
            unset($_ENV[$k], $_SERVER[$k]);
        }
        putenv('NO_PROXY=*');
        putenv('no_proxy=*');
        $ch = curl_init($upstream);
        curl_setopt_array($ch, [
            CURLOPT_RETURNTRANSFER => true,
            CURLOPT_FOLLOWLOCATION => true,
            CURLOPT_CONNECTTIMEOUT => 10,
            CURLOPT_TIMEOUT => 30,
            CURLOPT_PROXY => '',
            CURLOPT_NOPROXY => '*',
            CURLOPT_SSL_VERIFYPEER => false,
            CURLOPT_SSL_VERIFYHOST => 0,
            CURLOPT_USERAGENT => 'lemma-codecogs-proxy/1.1',
        ]);
        $body2 = curl_exec($ch);
        $code2 = (int) curl_getinfo($ch, CURLINFO_HTTP_CODE);
        $ctype2 = (string) curl_getinfo($ch, CURLINFO_CONTENT_TYPE);
        $err2 = curl_error($ch);
        curl_close($ch);
        if ($body2 !== false && $body2 !== '' && $code2 === 200) {
            $body = $body2;
            $code = $code2;
            if ($ctype2 !== '')
                $ctype = $ctype2;
            $err = '';
        } else {
            $err = $err !== '' ? $err : ($err2 !== '' ? $err2 : "curl exit $ret; upstream $code; php-curl $code2");
            if ($joined !== '' && $err === '')
                $err = $joined;
        }
    } else {
        $err = $joined !== '' ? $joined : ("curl exit $ret; upstream HTTP $code");
    }
}

if ($body === false || $body === '' || $code !== 200) {
    http_response_code(502);
    header('Content-Type: text/plain; charset=utf-8');
    echo $err !== '' ? $err : ("upstream HTTP $code");
    exit;
}

if (strncmp($body, "\x89PNG", 4) !== 0 && strncmp($body, "GIF8", 4) !== 0) {
    if ($ctype === '' || !str_starts_with(strtolower($ctype), 'image/')) {
        // sniff content-type from body if possible; otherwise reject HTML
        if (str_starts_with(ltrim($body), '<') || str_starts_with($body, '{')) {
            http_response_code(502);
            header('Content-Type: text/plain; charset=utf-8');
            echo 'upstream returned non-image';
            exit;
        }
    }
}

header('Content-Type: ' . ($ctype !== '' ? $ctype : 'image/png'));
header('Cache-Control: public, max-age=86400');
header('X-Content-Type-Options: nosniff');
echo $body;
