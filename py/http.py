import json, requests
import regex as re
from json.decoder import JSONDecodeError
from json import loads

def iter_lines(response):
    for line in response.iter_lines():
        line = line.decode('utf-8')
        if line.startswith('data:'):
            line = line[5:]
            try:
                yield loads(line)
            except JSONDecodeError:
                yield line

def json_post(url, json, headers={}, stream=False):
    try:
        headers['Content-Type'] = "application/json"
        if stream:
            headers['Accept'] = 'text/event-stream'
        response = requests.post(
            url,
            json=json,
            headers=headers,
            stream=stream
        )
        if stream:
            return iter_lines(response)
        text = response.text
        try:
            return loads(text)
        except JSONDecodeError:
            return text
    except Exception as e:
        return e


def curl_json_post(url, data):
    data = json.dumps(data, ensure_ascii=False)
    data = re.sub(r'(?<!\\)[\\]"', r"\\u0022", data)
    # data = re.sub(r'(?<!\\)"', '\\"', data)
    data = re.sub(r"(?<!\\)'", r"\\u0027", data)
    data = re.sub(r"(?<!\\)(([\\][\\])+)(?!\\)", r"\1\1", data)
    data = re.sub(r"[$]", "\\$", data)
    data = re.sub(r"[`]", "\\`", data)

    return f"curl -H 'Content-Type: application/json' -d '{data}' -X POST '{url}'"
    
def get(url, **kwargs):
    import regex as re
    if kwargs:
        url += "?"
        parameters = []
        for key, value in kwargs.items():
            if isinstance(value, str):
                value = re.sub(r'\+', '%2B', value)

            parameters.append(f"{key}={value}")
        url += '&'.join(parameters)

    text = requests.get(url).text
    try:
        return loads(text)
    except JSONDecodeError:
        return text
    
def form_post(url, data):
    for key, value in data.items():
        if not isinstance(value, str):
            data[key] = json.dumps(value, ensure_ascii=False)
            
    text = requests.post(
        url,
        data=data,
        headers={"Content-Type": "application/x-www-form-urlencoded; charset=UTF-8"}).text
    try:
        return loads(text)
    except JSONDecodeError:
        return text


def octet_stream_post(url, filename, data):
    text = requests.post(
        url,
        data=data,
        headers={"Content-Type": "application/octet-stream", 'filename': filename, 'Content-Length': str(len(data))}).text
    try:
        return loads(text)
    except JSONDecodeError:
        return text

def getParameters(request):
    #from flask.globals import request
    return {**request.args} | {**request.form} or {**request.json}


if __name__ == '__main__':
    curl = curl_json_post('http://192.168.18.131:5001/RLHFlow/Llama3-8B-v0.1/reward', {"prompt": "1 + 1 = ?", "answer": "1 + 1 = 2"})
    print(curl)
