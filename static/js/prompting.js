import {remove_capture, balanced_matchAll} from "./regexp.js"

export const X_Ai_Engine = {
    deepseek: [
        'deepseek-v3',
        'deepseek-r1',
        'deepseek-chat',
        'deepseek-reasoner'
    ],
    azure: [
        'gpt-3.5-turbo',
        'gpt-3.5-turbo-1106',
        'gpt-3.5-turbo-16k',
        'gpt-4',
    ],
    openai: [
        'gpt-4-turbo',
        'gpt-4o',
        'gpt-4o-mini',
        'gpt-4o-2024-11-20',
        'o1-preview',
        'o1-mini',
        'o1',
    ],
    anthropic: [
        'claude-3-sonnet',
        'claude-3-haiku',
        'claude-3-opus',
        'claude-3.5-sonnet',
        'claude-3.5-haiku'
    ],
    google: [
        'gemini-1.5-pro',
        'gemini-1.5-flash',
        'gemini-2.0-flash-exp',
    ],
    microsoft: [
        'phi-4',
    ],
};

const chat_template = `<|start_header_id|>%s<|end_header_id|>

%s<|eot_id|>`;

function apply_chat_template(message, role='assistant') {
    if (!message.isArray)
        message = [{role: 'user', content: message}];
    return message.map(message => chat_template.format(message.role, message.content)).join('') + chat_template.format(role, '%s').split('%s')[0];
}

function get_url(model, stream, kwargs) {
    var temperature = null;
    var top_p = null;
    var {repetition_penalty} = kwargs;
    switch(model) {
    case 'o1-preview':
    case 'o1-mini':
        temperature = 1;
        top_p = 1;
    case 'deepseek-chat':
    case 'deepseek-reasoner':
        return {
            method: json_post,
            url: 'https://api.deepseek.com/chat/completions',
            data(message) {
                if (message.isArray)
                    var [message, messages] = [null, message];
                else
                    messages = null;
                return {
                    message,
                    messages,
                    model,
                    stream,
                };
            },
            header,
        };

    default:
        temperature ||= 0.7;
        top_p ||= 0.9;
        var header = null;
        for (var engine in X_Ai_Engine){
            if (X_Ai_Engine[engine].contains(model)) {
                header = {'X-Ai-Engine': engine};
                break;
            }
        }
        return {
            method: json_post,
            url: 'http://rd-gateway.patsnap.io/compute/openai_chatgpt_turbo',
            data(message) {
                if (message.isArray)
                    var [message, messages] = [null, message];
                else
                    messages = null;
                return {
                    message,
                    messages,
                    model,
                    stream,
                    // role: "user",
                    // stop: null,
                    // n: 1,
                    max_tokens: 16384,
                    // frequency_penalty: 0,
                    // presence_penalty: 0,
                    // temperature,
                    // top_k: 40,
                    // top_p,
                };
            },
            header,
        };
    }
}

var Authorization = null;
export async function generate(message, model, stream, kwargs = {}) {
	console.log(`${model.toUpperCase()}: ${message.isString? message: JSON.stringify(message, null, 2)}`);
    var {method, url, data, header} = get_url(model, stream == null? false : true, kwargs);
    if (!Authorization) {
        switch (model) {
        case 'deepseek-chat':
        case 'deepseek-reasoner':
            var company = 'DeepSeek';
            break;
        default:
            var company = 'MyCompany';
        }
        Authorization = await form_post('php/request/authorization.php', {company});
    }
    var headers = {Authorization};

    if (header)
        Object.assign(headers, header);

    return await method(url, data(message), headers, stream);
}


export function parse_token(data, think) {
    if (data == 'finish' || data == '[DONE]')
        return;

    data = JSON.parse(data);
    var {choices, generated_text, token} = data;
    if (choices) {
        var [{delta: {content: text, reasoning_content}}] = choices;
        if (think)
            think.reasoning_content = reasoning_content;        
/*        if (think) {
            think.reasoning_content = reasoning_content;
            if (reasoning_content)
                return reasoning_content;
        }*/
    }
    else {
        if (generated_text)
            return;
        var {text} = token;
    }
    return text;
}

console.log('import prompting.js');
